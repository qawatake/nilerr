package nilerr

import (
	"fmt"
	"go/token"
	"go/types"
	"maps"

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

	var visit func(b *ssa.BasicBlock, f fact, assigned map[*ssa.Alloc]ssa.Value)

	for _, fn := range funcs {
		seen := make([]bool, len(fn.Blocks)) // seen[i] means visit should ignore block i
		visit = func(b *ssa.BasicBlock, f fact, assigned map[*ssa.Alloc]ssa.Value) {
			if seen[b.Index] {
				return
			}
			seen[b.Index] = true
			for _, instr := range b.Instrs {
				switch instr := instr.(type) {
				case *ssa.Store:
					if alloc, ok := instr.Addr.(*ssa.Alloc); ok {
						assigned[alloc] = instr.Val
					}
				}
			}
			switch f.kind {
			case precededByErrNeqNil:
				if ret := isReturnNil(b, assigned); ret != nil {
					if !usesErrorValue(b, f.value) {
						reportFail(f.value, ret, "error is not nil (%s) but it returns nil")
					}
				}
			case precededByErrEqNil:
				if ret := isReturnError(b, f.value, assigned); ret != nil {
					reportFail(f.value, ret, "error is nil (%s) but it returns error")
				}
			default:
				if vv := binOpErrNil(b, token.NEQ); vv != nil {
					a := maps.Clone(assigned)
					visit(b.Succs[0], fact{value: vv, kind: precededByErrNeqNil}, a)
					return
				} else if vv := binOpErrNil(b, token.EQL); vv != nil {
					if len(b.Succs[0].Preds) == 1 { // if there are multiple conditions, this may be false positive
						a := maps.Clone(assigned)
						visit(b.Succs[0], fact{value: vv, kind: precededByErrEqNil}, a)
						return
					}
				}
				for _, d := range b.Dominees() {
					a := maps.Clone(assigned)
					visit(d, fact{}, a)
				}
			}
		}
		for _, b := range fn.Blocks {
			visit(b, fact{}, map[*ssa.Alloc]ssa.Value{})
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

func isReturnNil(b *ssa.BasicBlock, assigned map[*ssa.Alloc]ssa.Value) *ssa.Return {
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
		case *ssa.UnOp:
			if v.Op == token.MUL {
				if alloc, ok := v.X.(*ssa.Alloc); ok {
					c, ok := assigned[alloc].(*ssa.Const)
					if ok && c.IsNil() {
						continue
					}
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

func isReturnError(b *ssa.BasicBlock, errVal ssa.Value, assigned map[*ssa.Alloc]ssa.Value) *ssa.Return {
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
		if alloc(v) != nil && alloc(errVal) != nil && alloc(v) == alloc(errVal) {
			return ret
		}
		if alloc(v) != nil && alloc(errVal) == nil && assigned[alloc(v)] == errVal {
			return ret
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
