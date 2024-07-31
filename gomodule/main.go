package main

import (
	"fmt"
	"sort"
	"math"
	"sync"
	"strings"
	"runtime"
	"unicode"
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
func(a Alphabet) Join(b Alphabet) Alphabet {
	c := append( Alphabet{}, a... )
	for _, x := range b {
		if !c.Contains(x) {
			c = append( c, x )
		}
	}
	sort.Sort(c)
	return c
}
func(a Alphabet) Values(m Model) map[string]bool {
	v := map[string]bool{}
	for i := range a {
		v[a[i]] = m[i]
	}
	return v
}

type Relation map[string]string

type Table map[string][]map[string]interface{}

type Model []bool
func(m Model) String() string {
	s := []string{}
	for _, b := range m {
		i := 0
		if b { i = 1 }
		s = append(s, fmt.Sprintf("%d", i))
	}

	return strings.Join(s, "")
}
func(a Model) equals(b Model) bool {
	if len(a) != len(b) { return false }
	for i := range a {
		if a[i] != b[i] { return false }
	}
	return true
}

type Profile []uint
func(a Profile) equals(b Profile) bool {
	if len(a) != len(b) { return false }
	for i := range a {
		if a[i] != b[i] { return false }
	}
	return true
}
func(p Profile) String() string {
	s := []string{}
	for _, pi := range p {
		s = append(s, fmt.Sprintf("%d", pi))
	}

	return strings.Join(s, ", ")
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
	GetAlphabet() Alphabet
}

type VarExpr struct {
	Name string
}

func (v VarExpr) GetAlphabet() Alphabet {
	return Alphabet{v.Name}
}

func (v VarExpr) Eval(vars map[string]bool) bool {
	return vars[v.Name]
}

type NotExpr struct {
	Expr Expr
}

func (v NotExpr) GetAlphabet() Alphabet {
	return v.Expr.GetAlphabet()
}
func (n NotExpr) Eval(vars map[string]bool) bool {
	return !n.Expr.Eval(vars)
}

type ImpliesExpr struct {
	Left, Right Expr
}

func (v ImpliesExpr) GetAlphabet() Alphabet {
	return v.Left.GetAlphabet().Join(v.Right.GetAlphabet())
}
func (n ImpliesExpr) Eval(vars map[string]bool) bool {
	return !n.Left.Eval(vars) || n.Right.Eval(vars)
}

type AndExpr struct {
	Left, Right Expr
}

func (v AndExpr) GetAlphabet() Alphabet {
	return v.Left.GetAlphabet().Join(v.Right.GetAlphabet())
}

func (a AndExpr) Eval(vars map[string]bool) bool {
	return a.Left.Eval(vars) && a.Right.Eval(vars)
}

type OrExpr struct {
	Left, Right Expr
}

func (v OrExpr) GetAlphabet() Alphabet {
	return v.Left.GetAlphabet().Join(v.Right.GetAlphabet())
}

func (o OrExpr) Eval(vars map[string]bool) bool {
	return o.Left.Eval(vars) || o.Right.Eval(vars)
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
}
func ParseFormula(s string) Formula {
	fmt.Printf("Parsing %s...\n", s)
	parser := NewParser(tokenize(s))
	expr := parser.parseExpr()
	//fmt.Printf("Parsing %s done", s)
	return Formula{str: s, expr: expr}
}
func(f Formula) Eval(values map[string]bool) bool {
	return f.expr.Eval(values)
}
func(f Formula) String() string {
	return f.str
}
func(f Formula) Parts() []Formula {
	fs := []Formula{}
	for _, x := range strings.Fields(f.String()) {
		fs = append( fs, ParseFormula(x) )
	}
	return fs
}
func(f Formula) GetAlphabet() Alphabet {
	return f.expr.GetAlphabet()
}
func(f Formula) GetModels() []Model {
	alph := f.GetAlphabet()

	models := []Model{}
	//models := make([]Model, int(math.Pow(2, float64(len(alph)))))
	for i := 0 ; i < int(math.Pow(2, float64(len(alph)))) ; i++ {
		m := make(Model, len(alph))
		for j := 0; j < len(alph); j++ {
			m[j] = (i>>j)&1 == 1
		}
		if f.Eval(alph.Values(m)) {
			models = append( models, m )
		}
	}
	return models
}


///////////////////////////////////////

var relations = []Relation{
	{"Employee.dept_id": "Department.id"},
}

var tables = Table{
	"Employee": {
		{"id": 1, "dept_id": 1, "name": "Bob"},
		{"id": 2, "dept_id": 1, "name": "Alice"},
		{"id": 3, "dept_id": 2, "name": "Hank"},
		{"id": 4, "dept_id": 3, "name": "Jane"},
		{"id": 5, "dept_id": 4, "name": "Frank"},
		{"id": 6, "dept_id": 5, "name": "Herbert"},
		{"id": 7, "dept_id": 6, "name": "Jodie"},
		{"id": 8, "dept_id": 6, "name": "Peter"},
		{"id": 9, "dept_id": 6, "name": "Heidi"},
	},
	"Department": {
		{"id": 1, "name": "Engineering"},
		{"id": 2, "name": "HR"},
		{"id": 3, "name": "Marketing"},
		{"id": 4, "name": "IT"},
		{"id": 5, "name": "RnD"},
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

func main() {
	//runtime.GOMAXPROCS(runtime.NumCPU())
	runtime.GOMAXPROCS(runtime.NumCPU() * 2)

	formulae := []Formula{}
	for _, rel := range relations {
		for src, dest := range rel {
			srcParts := strings.Split(src, ".")
			destParts := strings.Split(dest, ".")
			t, tc := srcParts[0], srcParts[1]
			t2, t2c := destParts[0], destParts[1]
			for _, row := range tables[t] {
				tv := row[tc].(int)
				f := fmt.Sprintf("%s__%s__%d", t, tc, tv)
				formulae = append(formulae, ParseFormula(f))

				t2n := fmt.Sprintf("%s__%s__%d", t2, t2c, tv)
				found := false
				for _, r := range tables[t2] {
					if r[t2c].(int) == tv {
						found = true
						break
					}
				}
				if found {
					formulae = append(formulae, ParseFormula(t2n))
				} else {
					formulae = append(formulae, ParseFormula("~"+t2n))
				}
			}
		}
	}

	constraintMap := map[string]bool{}
	for _, rel := range relations {
		for src, dest := range rel {
			srcParts := strings.Split(src, ".")
			destParts := strings.Split(dest, ".")
			t, tc := srcParts[0], srcParts[1]
			t2, t2c := destParts[0], destParts[1]
			for _, row := range tables[t] {
				tv := row[tc].(int)
				constraintMap[fmt.Sprintf("%s__%s__%d > %s__%s__%d", t, tc, tv, t2, t2c, tv)] = true
			}
		}
	}
	constraints := []Formula{}
	for f := range constraintMap {
		constraints = append(constraints, ParseFormula(f))
	}

	////////////////// 
	if false {
		formulae = []Formula{
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

		constraints = []Formula{
		}

	} else if false {
		formulae = []Formula{
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

		constraints = []Formula{
		}
	}

	//alphabet := generateAlphabet(formulae, constraints)
	alphabet := Alphabet{}
	for _, f := range append( formulae, constraints... ) {
		alphabet = alphabet.Join( f.GetAlphabet() )
	}

	fmt.Printf("Knowledgebase\nAlphabet: %s\n", strings.Join(alphabet, ", "))
	fmt.Printf("\nFormulae:\n")
	for _, f := range formulae {
		fmt.Printf("%v\n", f)
	}
	fmt.Printf("\nConstraints:\n")
	for _, c := range constraints {
		fmt.Printf("%v\n", c)
	}
	fmt.Println()

	distanceBasedInconsistency(formulae, constraints, alphabet)
}

type distanceBasedInconsistencyForProfileResult struct {
	consistentProfiles []Profile
	profileFrontier []Profile
}
var passedFrontierMutex sync.Mutex
func distanceBasedInconsistencyForProfiles( 
	profiles []Profile, 
	formulae []Formula, 
	constraints []Formula, 
	undilatedModels [][]Model,
	alphabet Alphabet,
	passedFrontier map[string]bool,
	ch chan<- distanceBasedInconsistencyForProfileResult,
) {

	//fmt.Printf("distanceBasedInconsistencyForProfiles(%d)...\n", len(profiles))

	res := distanceBasedInconsistencyForProfileResult{
		consistentProfiles: []Profile{},
		profileFrontier: []Profile{},
	}

	for _, profile := range profiles {

		fmt.Printf("Profile %v\r", profile)
		passedFrontierMutex.Lock()
		passedFrontier[profile.String()] = true
		passedFrontierMutex.Unlock()

		dilatedModels := [][]Model{}
		for i := 0; i < len(formulae); i++ {
			if profile[i] == 0 {
				dilatedModels = append( dilatedModels, undilatedModels[i] )

			} else {
				dilatedModels = append(dilatedModels, dilateModels(undilatedModels[i], profile[i]))
			}
		}

		intersect := modelIntersection(dilatedModels)
		if consistent := len(intersect) > 0 ; consistent {
			if !(containsProfile(res.consistentProfiles, profile)) {
				res.consistentProfiles = append(res.consistentProfiles, profile)
			}
		}

		passedFrontierMutex.Lock()
		for _, p := range incrementProfile(formulae, profile, alphabet, passedFrontier) {
			res.profileFrontier = append(res.profileFrontier, p)
		}
		passedFrontierMutex.Unlock()

	}

	ch<-res
}

func except(a []Profile, b map[string]bool) (res []Profile) {
	for i := range a {
		if b[a[i].String()] == false {
			res = append( res, a[i] )
		}
	}
	return res
}

func distanceBasedInconsistency(formulae []Formula, constraints []Formula, alphabet Alphabet) {

	undilatedModels := [][]Model{}
	for _, phi := range append(formulae, constraints...) {
		m := phi.GetModels()
		if len(m) == 0 {
			fmt.Printf("Precondition failed: knowledgebase contains individually inconsistent formula '%s'\n", phi)
			return
		}
		undilatedModels = append( undilatedModels, m )
		//for i := range m {
			//fmt.Printf("%v: %d: '%v'\n", phi, i, m[i])
		//}
	}

	profileFrontier := []Profile{make(Profile, len(formulae))}
	passedFrontier := map[string]bool{}
	consistentProfiles := []Profile{}
	ch := make(chan distanceBasedInconsistencyForProfileResult) //runtime.NumCPU())
	for len(profileFrontier) > 0 {
		chunkSize := int(float64(len(profileFrontier))/float64(runtime.NumCPU()))
		if chunkSize == 0 { chunkSize = 1 }
		fmt.Printf("%d passed, %d frontier, chunk size %d                                     \x1b[s\n", len(passedFrontier), len(profileFrontier), chunkSize)
		procCount := 0
		for i := 0 ; i < len(profileFrontier) ; i += chunkSize {
			i2 := i+chunkSize
			if i2 > len(profileFrontier) { i2 = len(profileFrontier) }
			go distanceBasedInconsistencyForProfiles( profileFrontier[i:i2], formulae, constraints, undilatedModels, alphabet, passedFrontier, ch )
			procCount += 1
		}
		profileFrontier = []Profile{}
		results := []distanceBasedInconsistencyForProfileResult{}
		for i := 0 ; i < procCount ; i += 1 {
			results = append( results, <-ch )
		}
		for _, res := range results {
			consistentProfiles = append( consistentProfiles, res.consistentProfiles... )
			for _, p := range res.profileFrontier {
				present := false
				for _, p2 := range profileFrontier {
					if p.equals(p2) { present = true; break }
				}

				if !(present) {
					profileFrontier = append( profileFrontier, res.profileFrontier... )
				}
			}
		}
	}
	fmt.Printf("\x1b[s\n")

	minProfiles := []Profile{}
	for _, curProfile := range consistentProfiles {
		isMinimal := true
		for _, p := range consistentProfiles {
			if !profilesEqual(p, curProfile) && isSubset(p, curProfile) {
				isMinimal = false
				break
			}
		}
		if isMinimal {
			minProfiles = append(minProfiles, curProfile)
		}
	}

	fmt.Println()

	var minIsum, minImax, minIhit *uint
	for _, minProfile := range minProfiles {
		Isum := uint(sum(minProfile))
		Imax := uint(max(minProfile))
		Ihit := uint(countPositive(minProfile))
		fmt.Printf("P_min: %v \tI_sum: %d, \tI_max: %d, \tI_hit: %d\n", minProfile, Isum, Imax, Ihit)
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

func dilateModels(models []Model, k uint) []Model {
	dilatedModels := []Model{}
	for i := range models {
		for _, dm := range dilateModel(models[i], k) {
			if !(containsModel(dilatedModels, dm)) {
				dilatedModels = append( dilatedModels, dm )
			}
		}
	}
	return dilatedModels
}

func dilateModel(model Model, k uint) []Model {
	dilated := []Model{model}
	for k > 0 {
		k--
		newModels := []Model{}
		for _, m := range dilated {
			for i := range m {
				md := make(Model, len(m))
				copy(md, m)
				md[i] = !md[i]

				if !(containsModel(dilated, md)) {
					newModels = append(newModels, md)
				}
			}
		}
		dilated = newModels
	}
	return dilated
}

func containsProfile(ps []Profile, p Profile) bool {
	for i := range ps {
		if ps[i].equals(p) { return true }
	}
	return false
}

func containsModel(ms []Model, m Model) bool {
	for i := range ms {
		if ms[i].equals(m) { return true }
	}
	return false
}

func modelIntersection(models [][]Model) []Model {
	if len(models) == 0 { return []Model{} }

	intersection := models[0]
	for _, curModels := range models[1:] {
		newIntersection := []Model{}
		for _, intersectionModel := range intersection {
			for _, curModel := range curModels {
				if intersectionModel.equals(curModel) {
					newIntersection = append(newIntersection, intersectionModel)
					break
				}
			}
		}
		intersection = newIntersection
		if len(intersection) == 0 { return []Model{} }
	}
	return intersection
}

func incrementProfile(formulae []Formula, profile Profile, alphabet Alphabet, passedFrontier map[string]bool) []Profile {

	//fmt.Printf("\nincrement %v\n", profile)
	var result []Profile
	for i := 0; i < len(formulae); i++ {
		if profile[i] >= uint(len(formulae[i].GetAlphabet())) { continue }

		newProfile := make(Profile, len(profile))
		copy(newProfile, profile)
		newProfile[i]++

		if passedFrontier[newProfile.String()] == false {
			passedFrontier[newProfile.String()] = true
			result = append(result, newProfile)
			//fmt.Printf("\tincremented %v\n", newProfile)
			//fmt.Printf("\nnew: %v\n", newProfile)
		}

	}
	return result
}

func sum(arr Profile) uint {
	var total uint = 0
	for _, v := range arr {
		total += v
	}
	return total
}

func max(arr Profile) uint {
	maxValue := arr[0]
	for _, v := range arr {
		if v > maxValue {
			maxValue = v
		}
	}
	return maxValue
}

func countPositive(arr Profile) int {
	count := 0
	for _, v := range arr {
		if v > 0 {
			count++
		}
	}
	return count
}

func profilesEqual(a, b Profile) bool {
	for i := range a {
		if i >= len(b) || a[i] != b[i] {
			return false
		}
	}
	return true
}

func isSubset(a, b Profile) bool {
	for i := range a {
		if a[i] > b[i] {
			return false
		}
	}
	return true
}


