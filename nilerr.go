package nilerr

import (
	"fmt"
	"go/token"
	"go/types"

	"github.com/gostaticanalysis/comment"
	"github.com/gostaticanalysis/comment/passes/commentmap"
	"golang.org/x/tools/go/analysis"
	"golang.org/x/tools/go/analysis/passes/buildssa"
	"golang.org/x/tools/go/ssa"
)

var Analyzer = &analysis.Analyzer{
	Name: "nilerr",
	Doc:  Doc,
	Run:  run,
	Requires: []*analysis.Analyzer{
		buildssa.Analyzer,
		commentmap.Analyzer,
	},
}

const Doc = "nilerr checks returning nil when err is not nil"

func run(pass *analysis.Pass) (interface{}, error) {
	funcs := pass.ResultOf[buildssa.Analyzer].(*buildssa.SSA).SrcFuncs
	cmaps := pass.ResultOf[commentmap.Analyzer].(comment.Maps)

	reportFail := func(v ssa.Value, ret *ssa.Return, format string) {
		pos := ret.Pos()
		line := getNodeLineNumber(pass, ret)
		errLines := getValueLineNumbers(pass, v)
		if !cmaps.IgnoreLine(pass.Fset, line, "nilerr") {
			var errLineText string
			if len(errLines) == 1 {
				errLineText = fmt.Sprintf("line %d", errLines[0])
			} else {
				errLineText = fmt.Sprintf("lines %v", errLines)
			}
			pass.Reportf(pos, format, errLineText)
		}
	}

	var visit func(b *ssa.BasicBlock, f fact)

	for _, fn := range funcs {
		a := make(assignments)
		for _, b := range fn.Blocks {
			for _, instr := range b.Instrs {
				if store, ok := instr.(*ssa.Store); ok {
					a.add(store)
				}
			}
		}
		seen := make([]bool, len(fn.Blocks)) // seen[i] means visit should ignore block i
		visit = func(b *ssa.BasicBlock, f fact) {
			if seen[b.Index] {
				return
			}
			seen[b.Index] = true
			switch f.kind {
			case precededByErrNeqNil:
				if ret := isReturnNil(b, a); ret != nil {
					if !usesErrorValue(b, f.value) {
						reportFail(f.value, ret, "error is not nil (%s) but it returns nil")
					}
				}
			case precededByErrEqNil:
				if ret := isReturnError(b, f.value, a); ret != nil {
					reportFail(f.value, ret, "error is nil (%s) but it returns error")
					return
				}
			default:
				if vv := binOpErrNil(b, token.NEQ); vv != nil {
					visit(b.Succs[0], fact{value: vv, kind: precededByErrNeqNil})
					return
				} else if vv := binOpErrNil(b, token.EQL); vv != nil {
					if len(b.Succs[0].Preds) == 1 { // if there are multiple conditions, this may be false positive
						visit(b.Succs[0], fact{value: vv, kind: precededByErrEqNil})
						return
					}
				}
				for _, d := range b.Dominees() {
					visit(d, fact{})
				}
			}
		}
		for _, b := range fn.Blocks {
			visit(b, fact{})
		}
	}

	return nil, nil
}

type fact struct {
	kind  kind
	value ssa.Value
}

type kind int

const (
	none                kind = 0
	precededByErrNeqNil kind = 1
	precededByErrEqNil  kind = 2
)

func cloneAssigned(assigned map[*ssa.Alloc]ssa.Value) map[*ssa.Alloc]ssa.Value {
	result := make(map[*ssa.Alloc]ssa.Value, len(assigned))
	for k, v := range assigned {
		result[k] = v
	}
	return result
}

func getValueLineNumbers(pass *analysis.Pass, v ssa.Value) []int {
	if phi, ok := v.(*ssa.Phi); ok {
		result := make([]int, 0, len(phi.Edges))
		for _, edge := range phi.Edges {
			result = append(result, getValueLineNumbers(pass, edge)...)
		}
		return result
	}

	value := v
	if extract, ok := value.(*ssa.Extract); ok {
		value = extract.Tuple
	}

	pos := value.Pos()
	return []int{pass.Fset.File(pos).Line(pos)}
}

func getNodeLineNumber(pass *analysis.Pass, node ssa.Node) int {
	pos := node.Pos()
	return pass.Fset.File(pos).Line(pos)
}

var errType = types.Universe.Lookup("error").Type().Underlying().(*types.Interface)

func binOpErrNil(b *ssa.BasicBlock, op token.Token) ssa.Value {
	if len(b.Instrs) == 0 {
		return nil
	}

	ifinst, ok := b.Instrs[len(b.Instrs)-1].(*ssa.If)
	if !ok {
		return nil
	}

	binop, ok := ifinst.Cond.(*ssa.BinOp)
	if !ok {
		return nil
	}

	if binop.Op != op {
		return nil
	}

	if !types.Implements(binop.X.Type(), errType) {
		return nil
	}

	if !types.Implements(binop.Y.Type(), errType) {
		return nil
	}

	xIsConst, yIsConst := isConst(binop.X), isConst(binop.Y)
	switch {
	case !xIsConst && yIsConst: // err != nil or err == nil
		return binop.X
	case xIsConst && !yIsConst: // nil != err or nil == err
		return binop.Y
	}

	return nil
}

func isConst(v ssa.Value) bool {
	_, ok := v.(*ssa.Const)
	return ok
}

func isReturnNil(b *ssa.BasicBlock, a assignments) *ssa.Return {
	if len(b.Instrs) == 0 {
		return nil
	}

	ret, ok := b.Instrs[len(b.Instrs)-1].(*ssa.Return)
	if !ok {
		return nil
	}

	errorReturnValues := 0
	for _, res := range ret.Results {
		if !types.Implements(res.Type(), errType) {
			continue
		}

		errorReturnValues++
		switch v := res.(type) {
		case *ssa.Const:
			if !v.IsNil() {
				return nil
			}
			continue
		case *ssa.UnOp: // 直前にnilをassignされている場合
			if x := alloc(v); x != nil {
				if c, ok := a.current(x, b.Instrs[len(b.Instrs)-1]).(*ssa.Const); ok && c.IsNil() {
					continue
				}
			}
			return nil
		default:
			return nil
		}
	}

	if errorReturnValues == 0 {
		return nil
	}

	return ret
}

func isReturnError(b *ssa.BasicBlock, errVal ssa.Value, a assignments) *ssa.Return {
	if len(b.Instrs) == 0 {
		return nil
	}

	ret, ok := b.Instrs[len(b.Instrs)-1].(*ssa.Return)
	if !ok {
		return nil
	}

	for _, v := range ret.Results {
		if v == errVal {
			return ret
		}
		if alloc(v) != nil || alloc(errVal) != nil {
			// returnされている値がif分岐の直後と同じ場合
			if a.current(alloc(v), b.Instrs[len(b.Instrs)-1]) == a.current(alloc(errVal), b.Instrs[0]) {
				return ret
			}
		}
	}

	return nil
}

// *t0 (t0 is a *ssa.Alloc) -> t0
// otherwise returns nil
func alloc(v ssa.Value) *ssa.Alloc {
	if unop, ok := v.(*ssa.UnOp); ok {
		if unop.Op == token.MUL {
			if alloc, ok := unop.X.(*ssa.Alloc); ok {
				return alloc
			}
		}
	}
	return nil
}

func usesErrorValue(b *ssa.BasicBlock, errVal ssa.Value) bool {
	for _, instr := range b.Instrs {
		if callInstr, ok := instr.(*ssa.Call); ok {
			for _, arg := range callInstr.Call.Args {
				if isUsedInValue(arg, errVal) {
					return true
				}

				sliceArg, ok := arg.(*ssa.Slice)
				if ok {
					if isUsedInSlice(sliceArg, errVal) {
						return true
					}
				}
			}
		}
	}
	return false
}

type ReferrersHolder interface {
	Referrers() *[]ssa.Instruction
}

var _ ReferrersHolder = (ssa.Node)(nil)
var _ ReferrersHolder = (ssa.Value)(nil)

func isUsedInSlice(sliceArg *ssa.Slice, errVal ssa.Value) bool {
	var valueBuf [10]*ssa.Value
	operands := sliceArg.Operands(valueBuf[:0])

	var valuesToInspect []ssa.Value
	addValueForInspection := func(value ssa.Value) {
		if value != nil {
			valuesToInspect = append(valuesToInspect, value)
		}
	}

	var nodesToInspect []ssa.Node
	visitedNodes := map[ssa.Node]bool{}
	addNodeForInspection := func(node ssa.Node) {
		if !visitedNodes[node] {
			visitedNodes[node] = true
			nodesToInspect = append(nodesToInspect, node)
		}
	}
	addReferrersForInspection := func(h ReferrersHolder) {
		if h == nil {
			return
		}

		referrers := h.Referrers()
		if referrers == nil {
			return
		}

		for _, r := range *referrers {
			if node, ok := r.(ssa.Node); ok {
				addNodeForInspection(node)
			}
		}
	}

	for _, operand := range operands {
		addReferrersForInspection(*operand)
		addValueForInspection(*operand)
	}

	for i := 0; i < len(nodesToInspect); i++ {
		switch node := nodesToInspect[i].(type) {
		case *ssa.IndexAddr:
			addReferrersForInspection(node)
		case *ssa.Store:
			addValueForInspection(node.Val)
		}
	}

	for _, value := range valuesToInspect {
		if isUsedInValue(value, errVal) {
			return true
		}
	}
	return false
}

func isUsedInValue(value, lookedFor ssa.Value) bool {
	if value == lookedFor {
		return true
	}
	if alloc(value) != nil && alloc(lookedFor) != nil && alloc(value) == alloc(lookedFor) {
		return true
	}

	switch value := value.(type) {
	case *ssa.ChangeInterface:
		return isUsedInValue(value.X, lookedFor)
	case *ssa.MakeInterface:
		return isUsedInValue(value.X, lookedFor)
	case *ssa.Call:
		if value.Call.IsInvoke() {
			return isUsedInValue(value.Call.Value, lookedFor)
		}
	}

	return false
}

// t0 : t11 -> t12 -> t13
// *t0 := t11
// *t0 := t12
// *t0 := t13
type assignments map[*ssa.Alloc][]*ssa.Store

func (a assignments) add(s *ssa.Store) {
	if s == nil {
		return
	}
	if to, ok := s.Addr.(*ssa.Alloc); ok {
		if alloc(s.Val) != to {
			a[to] = append(a[to], s)
		}
	}
}

func (a assignments) current(x *ssa.Alloc, instr ssa.Instruction) ssa.Value {
	stores := a[x]
	if len(stores) == 0 {
		return nil
	}
	b := instr.Block()
	for i := len(stores) - 1; i >= 0; i-- {
		s := stores[i]
		if !(s.Block().Dominates(b) || s.Block() == b) {
			continue
		}
		dominator := func(x, y ssa.Instruction) ssa.Instruction {
			for _, i := range b.Instrs {
				if i == x {
					return x
				}
				if i == y {
					return y
				}
			}
			return nil
		}(s, instr)
		if dominator != s {
			continue
		}
		return s.Val
	}
	return nil
}
