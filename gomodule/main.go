package main

import (
	"os"
	"log"
	"fmt"
	"sort"
	"sync"
	//"math"
	//"time"
	//"bufio"
	"strings"
	"runtime"
	"unicode"
	"runtime/pprof"
)

type Alphabet []string
func (a Alphabet) Len() int           { return len(a) }
func (a Alphabet) Swap(i, j int)      { a[i], a[j] = a[j], a[i] }
func (a Alphabet) Less(i, j int) bool { return a[i] < a[j] }
func(a Alphabet) Contains(s string) bool {
	for _, x := range a {
		if x == s { return true }
	}
	return false
}
func(a *Alphabet) Index(s string) int {
	for i, x := range *a {
		if x == s { return i }
	}
	panic(fmt.Sprintf("unknown variable '%v'", s))
}
func(a *Alphabet) Join(b *Alphabet) *Alphabet {
	c := append( Alphabet{}, (*a)... )
	for _, x := range *b {
		if !c.Contains(x) {
			c = append( c, x )
		}
	}
	sort.Sort(c)
	return &c
}
func(a *Alphabet) Values(m Model) map[string]bool {
	v := map[string]bool{}
	for i := range *a {
		v[(*a)[i]] = m[i] == '1'
	}
	return v
}

type Relation map[string]string

type Table map[string][]map[string]interface{}


type Model []byte
func NewModel(l int) *Model {
	b := make([]byte, l)
	for i := 0 ; i < l ; i++ { b[i] = '0' }
	m := Model(string(b))
	return &m
}
func(m *Model) Get(idx int) bool {
	return (*m)[idx] == '1'
}
func(m *Model) Set(idx int, v bool) {
	if v {
		(*m)[idx] = '1'
	} else {
		(*m)[idx] = '0'
	}
}
func(m *Model) CopyWith(idx int, val bool) *Model {
	l := make([]byte, len(*m), len(*m))
	copy(l, *m)

	if val { 
		l[idx] = '1'
	} else {
		l[idx] = '0'
	}

	res := Model(l)
	return &res
}
func(m *Model) String() string {
	return string(*m)
}

type Profile []uint
func(a Profile) Less(b Profile) bool {
	if len(a) != len(b) { panic("Incompatible profiles") }
	anySmaller := false
	for i := range a {
		if a[i] > b[i] {
			return false
		} else if a[i] < b[i] {
			anySmaller = true
		}
	}
	return anySmaller
}
func(a Profile) Equals(b Profile) bool {
	if len(a) != len(b) { panic("Incompatible profiles") }
	for i := range a {
		if a[i] != b[i] {
			return false
		}
	}
	return true
}
func(p Profile) Id() uint {
	s := uint(0)
	for i := len(p)-1 ; i >= 0 ; i-- {
		s += (1 << i) * p[i]
	}
	return s
}
func(p Profile) String() string {
	s := []string{}
	for _, pi := range p {
		s = append(s, fmt.Sprintf("%d", pi))
	}

	return strings.Join(s, ", ")
}
func(profile Profile) Increment(alphabet *Alphabet, formulae []*Formula) []*Profile {

	result := make([]*Profile, 0, len(profile)*len(*alphabet))
	for i := 0; i < len(formulae); i++ {
		if profile[i] >= uint(len(*formulae[i].GetAlphabet())) { continue }

		newProfile := make(Profile, len(profile))
		copy(newProfile, profile)
		newProfile[i]++

		result = append( result, &newProfile )

	}
	return result
}
func(p Profile) sum() uint {
	var total uint = 0
	for _, v := range p {
		total += v
	}
	return total
}

func(p Profile) max() uint {
	maxValue := p[0]
	for _, v := range p {
		if v > maxValue {
			maxValue = v
		}
	}
	return maxValue
}

func(p Profile) hit() int {
	count := 0
	for _, v := range p {
		if v > 0 {
			count++
		}
	}
	return count
}






/////////////////////////////

type TokenType int

const (
	TokenEOF TokenType = iota
	TokenAnd
	TokenOr
	TokenNot
	TokenImplies
	TokenLParen
	TokenRParen
	TokenVar
)

type Token struct {
	Type  TokenType
	Value string
}

func isSymbolElement(s byte) bool {
	return unicode.IsLetter(rune(s)) || unicode.IsNumber(rune(s)) || string(s) == "_"
}

func tokenize(input string) []Token {
	var tokens []Token
	i := 0
	for i < len(input) {
		switch {
		case input[i] == ' ':
			i++
		case input[i] == '&':
			tokens = append(tokens, Token{Type: TokenAnd})
			i++
		case input[i] == '|':
			tokens = append(tokens, Token{Type: TokenOr})
			i++
		case input[i] == '~':
			tokens = append(tokens, Token{Type: TokenNot})
			i++
		case input[i] == '(':
			tokens = append(tokens, Token{Type: TokenLParen})
			i++
		case input[i] == ')':
			tokens = append(tokens, Token{Type: TokenRParen})
			i++
		case input[i] == '>':
			tokens = append(tokens, Token{Type: TokenImplies})
			i++
		case isSymbolElement(input[i]):
			start := i
			for i < len(input) && isSymbolElement(input[i]) {
				i++
			}
			tokens = append(tokens, Token{Type: TokenVar, Value: input[start:i]})
		default:
			panic(fmt.Sprintf("unexpected character: %c", input[i]))
		}
	}
	tokens = append(tokens, Token{Type: TokenEOF})
	return tokens
}

type Expr interface {
	Eval(vars map[string]bool) bool
	Eval2(*Alphabet, *Model) bool
	GetAlphabet() *Alphabet
}

type VarExpr struct {
	Name string
}

func (v VarExpr) GetAlphabet() *Alphabet {
	return &Alphabet{v.Name}
}

func (v VarExpr) Eval(vars map[string]bool) bool {
	return vars[v.Name]
}
func (v VarExpr) Eval2(alphabet *Alphabet, model *Model) bool {
	return (*model)[alphabet.Index(v.Name)] == '1'
}

type NotExpr struct {
	Expr Expr
}

func (v NotExpr) GetAlphabet() *Alphabet {
	return v.Expr.GetAlphabet()
}
func (n NotExpr) Eval(vars map[string]bool) bool {
	return !n.Expr.Eval(vars)
}
func (n NotExpr) Eval2(alphabet *Alphabet, model *Model) bool {
	return !n.Expr.Eval2(alphabet, model)
}

type ImpliesExpr struct {
	Left, Right Expr
}

func (v ImpliesExpr) GetAlphabet() *Alphabet {
	al := v.Left.GetAlphabet()
	ar := v.Right.GetAlphabet()
	return al.Join(ar)
}
func (v ImpliesExpr) Eval(vars map[string]bool) bool {
	return !v.Left.Eval(vars) || v.Right.Eval(vars)
}
func (v ImpliesExpr) Eval2(alphabet *Alphabet, model *Model) bool {
	return !v.Left.Eval2(alphabet, model) || v.Right.Eval2(alphabet, model)
}

type AndExpr struct {
	Left, Right Expr
}

func (v AndExpr) GetAlphabet() *Alphabet {
	return v.Left.GetAlphabet().Join(v.Right.GetAlphabet())
}

func (a AndExpr) Eval(vars map[string]bool) bool {
	return a.Left.Eval(vars) && a.Right.Eval(vars)
}
func (a AndExpr) Eval2(alphabet *Alphabet, model *Model) bool {
	return a.Left.Eval2(alphabet, model) && a.Right.Eval2(alphabet, model)
}

type OrExpr struct {
	Left, Right Expr
}

func (v OrExpr) GetAlphabet() *Alphabet {
	return v.Left.GetAlphabet().Join(v.Right.GetAlphabet())
}

func (o OrExpr) Eval(vars map[string]bool) bool {
	return o.Left.Eval(vars) || o.Right.Eval(vars)
}
func (o OrExpr) Eval2(alphabet *Alphabet, model *Model) bool {
	return o.Left.Eval2(alphabet, model) || o.Right.Eval2(alphabet, model)
}

type Parser struct {
	tokens []Token
	pos    int
}

func NewParser(tokens []Token) *Parser {
	return &Parser{tokens: tokens, pos: 0}
}

func (p *Parser) parseExpr() Expr {
	return p.parseImplies()
}

func (p *Parser) parseOr() Expr {
	left := p.parseAnd()
	for p.match(TokenOr) {
		right := p.parseAnd()
		left = OrExpr{Left: left, Right: right}
	}
	return left
}

func (p *Parser) parseAnd() Expr {
	left := p.parseNot()
	for p.match(TokenAnd) {
		right := p.parseNot()
		left = AndExpr{Left: left, Right: right}
	}
	return left
}

func (p *Parser) parseNot() Expr {
	if p.match(TokenNot) {
		expr := p.parseNot()
		return NotExpr{Expr: expr}
	}
	return p.parsePrimary()
}

func (p *Parser) parseImplies() Expr {
	left := p.parseOr()
	for p.match(TokenImplies) {
		right := p.parseOr()
		//fmt.Printf("############ implies: %v > %v\n", left, right)
		left = ImpliesExpr{Left: left, Right: right}
	}
	return left
}

func (p *Parser) parsePrimary() Expr {
	if p.match(TokenLParen) {
		expr := p.parseExpr()
		p.expect(TokenRParen)
		return expr
	}
	if p.currentToken().Type == TokenVar {
		name := p.currentToken().Value
		p.nextToken()
		return VarExpr{Name: name}
	}
	panic("unexpected token")
}

func (p *Parser) match(expected TokenType) bool {
	if p.currentToken().Type == expected {
		p.nextToken()
		return true
	}
	return false
}

func (p *Parser) expect(expected TokenType) {
	if !p.match(expected) {
		panic(fmt.Sprintf("expected token: %v", expected))
	}
}

func (p *Parser) currentToken() Token {
	return p.tokens[p.pos]
}

func (p *Parser) nextToken() {
	p.pos++
}

//////////////////////////////////////

type Formula struct {
	expr Expr
	str string
	//models map[uint][]Model
	models map[uint][]Model
	modelsMap map[uint]map[string]*Model
	nonModelsMap map[uint]map[string]*Model
	modelsMutex sync.Mutex
	varIndices []int
}

func ParseFormula(s string) *Formula {
	//fmt.Printf("Parsing %s...\n", s)
	parser := NewParser(tokenize(s))
	expr := parser.parseExpr()
	f := Formula{
		str: s, 
		expr: expr, 
		models: map[uint][]Model{},
		modelsMutex: sync.Mutex{},
		varIndices: nil,
	}
	//fmt.Printf("Parsing %s done -> %p\n", s, &f)
	return &f
}
func(f *Formula) Eval(values map[string]bool) bool {
	return f.expr.Eval(values)
}
func(f *Formula) Eval2(alphabet *Alphabet, model *Model) bool {
	return f.expr.Eval2(alphabet, model)
}
func(f *Formula) String() string {
	return f.str
}
func(f *Formula) GetAlphabet() *Alphabet {
	return f.expr.GetAlphabet()
}
func(f *Formula) storeModels(k uint, m []Model) {
	f.modelsMutex.Lock(); defer f.modelsMutex.Unlock()
	tmp := make([]Model, len(m), len(m))
	copy(tmp, m)
	f.models[k] = tmp
}
func(f *Formula) loadModels(k uint) []Model {
	f.modelsMutex.Lock(); defer f.modelsMutex.Unlock()
	v := f.models[k]
	if v == nil { return nil }
	tmp := make([]Model, len(v), len(v))
	copy(tmp, v)
	return tmp
}
func(f *Formula) storeModelsMap(k uint, models map[string]*Model, nonModels map[string]*Model) {
	f.modelsMutex.Lock(); defer f.modelsMutex.Unlock()
	if f.modelsMap == nil { f.modelsMap = map[uint]map[string]*Model{} }
	if f.nonModelsMap == nil { f.nonModelsMap = map[uint]map[string]*Model{} }
	f.modelsMap[k] = models
	f.nonModelsMap[k] = nonModels
}
func(f *Formula) loadModelsMap(k uint) (map[string]*Model, map[string]*Model) {
	f.modelsMutex.Lock(); defer f.modelsMutex.Unlock()
	if f.modelsMap == nil { f.modelsMap = map[uint]map[string]*Model{} }
	if f.nonModelsMap == nil { f.nonModelsMap = map[uint]map[string]*Model{} }
	models := f.modelsMap[k]
	nonModels := f.nonModelsMap[k]
	return models, nonModels
}
func(f *Formula) getVarIndices(globalAlphabet *Alphabet) []int {
	if f.varIndices == nil { 
		phiAlphabet := f.GetAlphabet()
		res := make([]int, len(*globalAlphabet))
		j := 0
		for i, a := range *globalAlphabet {
			for _, b := range *phiAlphabet {
				if a == b {
					res[j] = i 
					j += 1
					break
				}
			}
		}
		f.varIndices = res[:j]
		//fmt.Printf("varIndices(%p = %v) = %v\n", f, f, f.varIndices)
	}
	return f.varIndices
}
func(f *Formula) dilateModel(k uint, alphabet *Alphabet) []Model {
	//fmt.Printf("dilateModel(%d, %p = %v, alph(%d))\n", k, f, f, len(alphabet))
	for l := uint(1) ; l <= k ; l++ {
		if m := f.loadModels(l) ; m == nil {
			toDilate := f.loadModels(l-1)
			//fmt.Printf("%v: dilating %d -> %d : %v\n", f, l-1, l, toDilate)
			dilatedMap := map[string]Model{}
			for _, m := range toDilate {
				for _, i := range f.getVarIndices(alphabet) {
					md := m.CopyWith(i, m[i] != '1')
					dilatedMap[md.String()] = *md
				}
			}

			dilated := make([]Model, len(dilatedMap))
			i := 0 
			for _, d := range dilatedMap {
				dilated[i] = d
				i += 1
			}
			//fmt.Printf("%v\n->\n%v\n", len(toDilate), len(dilated))
			//fmt.Printf("%v: dilating %d -> %d : %v\n", f, l-1, l, toDilate)
			//fmt.Printf("%v: dilated\n%d : %v ->\n%d : %v\n", f, len(toDilate), toDilate, len(dilated), dilated)
			f.storeModels(l, dilated)

			if l == k { return dilated }
		}
	}

	return f.loadModels(k)

}
func(f *Formula) GetModels(k uint, alphabet *Alphabet) []Model {
	//fmt.Printf("GetModels(%d, %p = %v, alph(%d))\n", k, f, f, len(alphabet))
	if baseModel := f.loadModels(0) ; baseModel == nil {
		modelCount := 1 << len(*alphabet)
		models := make([]Model, modelCount)
		mi := 0
		for i := 0 ; i < modelCount ; i++ {
			model := NewModel(len(*alphabet))
			for j := 0; j < len(*alphabet) ; j++ {
				//model[j] = (i>>j)&1 == 1
				model.Set(j, (i>>j)&1 == 1)
			}
			if f.Eval2(alphabet, model) {
				models[mi] = *model
				mi += 1
			}
		}
		//fmt.Printf("%v: %d base model: %v\n", f, len(models[:mi]), models[:mi])
		f.storeModels(0, models[:mi])
	}

	v := f.loadModels(k)
	if v != nil { return v }

	return f.dilateModel(k, alphabet)
}

func(f *Formula) GetModelsMap(k uint, alphabet *Alphabet) (map[string]*Model, map[string]*Model) {
	if baseModels, baseNonModels := f.loadModelsMap(0) ; baseModels == nil || baseNonModels == nil {
		modelCount := 1 << len(*alphabet)
		models := make(map[string]*Model, modelCount)
		nonModels := make(map[string]*Model, modelCount)
		for i := 0 ; i < modelCount ; i++ {
			model := NewModel(len(*alphabet))
			for j := 0; j < len(*alphabet) ; j++ {
				//model[j] = (i>>j)&1 == 1
				model.Set(j, (i>>j)&1 == 1)
			}
			if f.Eval2(alphabet, model) {
				models[string(*model)] = model
			} else {
				nonModels[string(*model)] = model
			}
		}
		f.storeModelsMap(0, models, nonModels)

		if k == 0 { return models, nonModels }
	}

	for l := uint(1) ; l <= k ; l++ {
		if models, nonModels := f.loadModelsMap(l) ; models == nil || nonModels == nil {
			toDilateModels, toDilateNonModels := f.loadModelsMap(l-1)
			dilatedModels := map[string]*Model{}
			dilatedNonModels := map[string]*Model{}
			for k, m := range toDilateNonModels { dilatedNonModels[k] = m }

			for _, m := range toDilateModels {
				for _, i := range f.getVarIndices(alphabet) {
					md := m.CopyWith(i, (*m)[i] != '1')
					dilatedModels[md.String()] = md
					delete(dilatedNonModels, md.String())
				}
			}

			f.storeModelsMap(l, dilatedModels, dilatedNonModels)

			if l == k { return dilatedModels, dilatedNonModels }
		}
	}

	return f.loadModelsMap(k)
}

///////////////////////////////////////

var relations = []Relation{
	{"Employee.dept_id": "Department.id"},
	{"Address.emp_id": "Employee.id"},
}

var tables = Table{
	"Employee": {
		{"id": 1, "dept_id": 1, "name": "Michael"},
		{"id": 2, "dept_id": 2, "name": "Jim"},
		{"id": 3, "dept_id": 2, "name": "Pam"},
		{"id": 4, "dept_id": 3, "name": "Erin"},
		{"id": 5, "dept_id": 4, "name": "Jan"},
		{"id": 6, "dept_id": 5, "name": "Andy"},
		{"id": 7, "dept_id": 6, "name": "Creed"},
		{"id": 8, "dept_id": 6, "name": "Dwight"},
		//{"id": 9, "dept_id": 6, "name": "Kevin"},
		//{"id": 10, "dept_id": 7, "name": "Kelly"},
	},
	"Department": {
		{"id": 1, "name": "Management"},
		{"id": 2, "name": "Sales"},
		{"id": 3, "name": "Accounting"},
		{"id": 4, "name": "HR"},
		//{"id": 5, "name": "Reception"},
	},
	"Address": {
		{"id": 1, "emp_id": 1, "address": "Sesame street 1"},
		{"id": 2, "emp_id": 2, "address": "Sesame street 2"},
		//{"id": 4, "emp_id": 11, "address": "Sesame street 4"},
	},
}

/*
var relations = []Relation{
	{"Employee.dept_id": "Department.id"},
}

var tables = Table{
	"Employee": {
		{"id": 1, "name": "Bob", "dept_id": 1},
		{"id": 2, "name": "Alice", "dept_id": 1},
		{"id": 3, "name": "Hank", "dept_id": 2},
		{"id": 4, "name": "Jane", "dept_id": 3},
	},
	"Department": {
		{"id": 1, "name": "Engineering"},
		{"id": 2, "name": "HR"},
		{"id": 3, "name": "Marketing"},
	},
}
*/

type distanceBasedInconsistencyForProfileResult struct {
	consistentProfiles []*Profile
	newFrontier []*Profile
}
//var _seenProfiles sync.Map
var _testedProfileCount int
func distanceBasedInconsistencyForProfiles( 
	ch chan<- distanceBasedInconsistencyForProfileResult,
	profiles []*Profile, 
	formulae []*Formula, 
	constraints []*Formula, 
	alphabet *Alphabet,
) {

	res := distanceBasedInconsistencyForProfileResult{
		consistentProfiles: []*Profile{},
		newFrontier: []*Profile{},
	}

	allPhi := append(formulae, constraints...)

	for _, profile := range profiles {

		_testedProfileCount++
		if _testedProfileCount % 100 == 0 {
			fmt.Printf("Profile %d\r", _testedProfileCount)
		}

		consistent := false
		phi0models, phi0nonModels := allPhi[0].GetModelsMap((*profile)[0], alphabet)
		if len(phi0models) > len(phi0nonModels) {

			modelIntersect := make(map[string]*Model, len(phi0models))
			for k, v := range phi0models { modelIntersect[k] = v }

			outerIntersect:
			for i := 1; i < len(allPhi) && len(modelIntersect) > 0 ; i++ {

				phiModels, _ := allPhi[i].GetModelsMap((*profile)[i], alphabet)
				for intersectStr := range modelIntersect {
					if phiModels[intersectStr] == nil {
						delete(modelIntersect, intersectStr)
						if len(modelIntersect) == 0 { break outerIntersect }
					}
				}
			}
			consistent = len(modelIntersect) > 0

		} else {

			nonModelJoin := make(map[string]*Model, 1<<len(*alphabet))
			for k, v := range phi0nonModels { nonModelJoin[k] = v }

			outerNonIntersect:
			for i := 1; i < len(allPhi) ; i++ {
				_, phiNonModels := allPhi[i].GetModelsMap((*profile)[i], alphabet)
				for modelStr, model := range phiNonModels {
					nonModelJoin[modelStr] = model
					if len(nonModelJoin) >= (1<<len(*alphabet)) { break outerNonIntersect }
				}
			}
			consistent = len(nonModelJoin) < (1<<len(*alphabet))
		}

		if consistent {
			//fmt.Printf("consistent (%v) model: %v\n", profile.String(), modelIntersect)
			res.consistentProfiles = append(res.consistentProfiles, profile)

		} else {
			for _, p := range profile.Increment(alphabet, formulae) {
				res.newFrontier = append(res.newFrontier, p)
			}
		}

	}

	ch<-res
}

func distanceBasedInconsistency(formulae []*Formula, constraints []*Formula, alphabet *Alphabet) {

	p0 := Profile{}
	for range len(formulae)+len(constraints) {
		p0 = append (p0, 0 )
	}
	profileFrontier := map[string]*Profile{} //make([]*Profile, 1, 1000)
	profileFrontier[p0.String()] = &p0
	consistentProfiles := map[string]*Profile{}
	ch := make(chan distanceBasedInconsistencyForProfileResult) //runtime.NumCPU())
	iteration := 0
	for len(profileFrontier) > 0 {
		iteration += 1
		blockSize := int(float64(len(profileFrontier))/float64(runtime.NumCPU()))
		if blockSize == 0 { blockSize = 1 }
		fmt.Printf("Iteration %d, frontier %d, block size %d                                                             \x1b[s\n", iteration, len(profileFrontier), blockSize)
		procCount := 0
		for len(profileFrontier) > 0 {
			if blockSize > len(profileFrontier) { blockSize = len(profileFrontier) }

			profileBlock := make([]*Profile, 0, blockSize)
			ks := []string{}
			for k := range profileFrontier { ks = append( ks, k ); if len(ks) >= blockSize { break } }
			for _, k := range ks {
				profileBlock = append( profileBlock, profileFrontier[k] )
				delete(profileFrontier, k)
			}
			go distanceBasedInconsistencyForProfiles( ch, profileBlock, formulae, constraints, alphabet )
			procCount += 1
		}

		for i := 0 ; i < procCount ; i += 1 {
			res := <-ch

			outerNewFrontier:
			for _, fp := range res.newFrontier {
				for _, cp := range consistentProfiles {
					if cp.Equals(*fp) || cp.Less(*fp) {
						continue outerNewFrontier
					}
				}
				profileFrontier[fp.String()] = fp
			}
			//fmt.Printf("job %d reported %d new frontier, %d consistent\n", i+1, len(res.newFrontier), len(res.consistentProfiles))

			outerConsistentProfiles:
			for _, newCP := range res.consistentProfiles {
				if consistentProfiles[newCP.String()] == nil {
					for _, cp := range consistentProfiles {
						if cp.Equals(*newCP) || cp.Less(*newCP) {
							continue outerConsistentProfiles
						}
					}
					consistentProfiles[newCP.String()] = newCP
				}
			}
		}
	}
	fmt.Printf("\x1b[s\n")

	ks := []string{}
	for k, _ := range consistentProfiles { ks = append( ks, k ) }
	sort.Strings(ks)

	var minIsum, minImax, minIhit *uint
	fmt.Printf("Tested %d profiles, found %d minimal consistent profiles\n", _testedProfileCount, len(consistentProfiles))
	for _, k := range ks {
		minProfile := consistentProfiles[k]
		Isum := uint(minProfile.sum())
		Imax := uint(minProfile.max())
		Ihit := uint(minProfile.hit())
		fmt.Printf("P_min: (%v) \tI_sum: %d, \tI_max: %d, \tI_hit: %d\n", minProfile, Isum, Imax, Ihit)
		if minIsum == nil || Isum < *minIsum {
			minIsum = &Isum
		}
		if minImax == nil || Imax < *minImax {
			minImax = &Imax
		}
		if minIhit == nil || Ihit < *minIhit {
			minIhit = &Ihit
		}
	}

	if minIsum != nil && minImax != nil && minIhit != nil {
		fmt.Printf("\nI_sum_min: %v, \tI_max_min: %v, \tI_hit_min: %v\n", *minIsum, *minImax, *minIhit)
	} else {
		fmt.Printf("\nEmpty result\n")
	}
}

const PROFILING = false
func main() {
	if PROFILING {
		f, err := os.Create("cpuprofile")
		if err != nil { log.Fatal(err) }
		pprof.StartCPUProfile(f)
		defer pprof.StopCPUProfile()
	}

	runtime.GOMAXPROCS(runtime.NumCPU())
	// for debugging
	//runtime.GOMAXPROCS(1)

	seenFormulae := map[string]bool{}
	formulaeStrs := []string{}
	for _, rel := range relations {
		for src, dest := range rel {
			srcParts := strings.Split(src, ".")
			destParts := strings.Split(dest, ".")
			t, tc := srcParts[0], srcParts[1]
			t2, t2c := destParts[0], destParts[1]
			for _, row := range tables[t] {
				tv := row[tc].(int)
				f := fmt.Sprintf("%s__%s__%d", t, tc, tv)
				if seenFormulae[f] == false {
					seenFormulae[f] = true
					formulaeStrs = append(formulaeStrs, f)
				}

				t2n := fmt.Sprintf("%s__%s__%d", t2, t2c, tv)
				danglingKey := true
				for _, r := range tables[t2] {
					if r[t2c].(int) == tv {
						danglingKey = false
						break
					}
				}
				if danglingKey {
					t2n = "~"+t2n
				}
				if seenFormulae[t2n] == false {
					seenFormulae[t2n] = true
					formulaeStrs = append(formulaeStrs, t2n)
				}
			}
		}
	}

	formulae := []*Formula{}
	sort.Strings(formulaeStrs)
	for _, f := range formulaeStrs {
		formulae = append( formulae, ParseFormula(f) )
	}

	constraints := []*Formula{}
	for _, rel := range relations {
		for src, dest := range rel {
			srcParts := strings.Split(src, ".")
			destParts := strings.Split(dest, ".")
			t, tc := srcParts[0], srcParts[1]
			t2, t2c := destParts[0], destParts[1]
			for _, row := range tables[t] {
				tv := row[tc].(int)
				s := fmt.Sprintf("%s__%s__%d > %s__%s__%d", t, tc, tv, t2, t2c, tv)
				if seenFormulae[s] == false {
					seenFormulae[s] = true
					constraints = append( constraints, ParseFormula(s) )
				}
			}
		}
	}


	////////////////// 
	if false {
		formulae = []*Formula{
			//"a & b",
			//"~a & ~b",

			/*
			"a",
			"~a | ~b",
			"b",\
			*/

			//ParseFormula("a & b & c"),
			//ParseFormula("~a & ~b & ~c"),

			ParseFormula("x & y"),
			ParseFormula("y & z"),
			ParseFormula("~z"),
		}

		constraints = []*Formula{
		}

	} else if false {
		formulae = []*Formula{
			//"a & b",
			//"~a & ~b",

			/*
			"a",
			"~a | ~b",
			"b",\
			*/
			ParseFormula("a"),
			ParseFormula("b"),
			ParseFormula("c"),
			ParseFormula("~a"),
			ParseFormula("~b"),
			ParseFormula("~c"),
		}

		constraints = []*Formula{
		}

	} else if false {
		formulae = []*Formula{
			//"a & b",
			//"~a & ~b",

			/*
			"a",
			"~a | ~b",
			"b",\
			*/
			ParseFormula("a & b & c"),
			ParseFormula("~a & ~b & ~c"),
		}

		constraints = []*Formula{
		}
	}

	//alphabet := generateAlphabet(formulae, constraints)
	alphabet := &Alphabet{}
	for i := range len(formulae) + len(constraints) {
		var f *Formula = nil
		if i < len(formulae) {
			f = formulae[i]
		} else {
			f = constraints[i-len(formulae)]
		}
		alphabet = alphabet.Join( f.GetAlphabet() )
	}

	fmt.Printf("Knowledgebase\nAlphabet: %s\n", strings.Join(*alphabet, ", "))
	//fmt.Printf("\nPotential profiles: %d\n", int(math.Pow(float64(len(formulae)), float64(len(alphabet)))))
	fmt.Printf("\nFormulae:\n")
	for i, f := range formulae {
		fmt.Printf("%d: %v\n", i+1, f)
	}
	fmt.Printf("\nConstraints:\n")
	for i, c := range constraints {
		fmt.Printf("%d: %v\n", len(formulae)+i+1, c)
	}
	fmt.Println()

	distanceBasedInconsistency(formulae, constraints, alphabet)
}

