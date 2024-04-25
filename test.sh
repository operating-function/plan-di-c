try () {
    echo EXAMPLE: $1
    echo $1 | ./plan
    echo
}

# # these tests will fail, since they are from the old spec. the seed files
# # here were also from the old spec - we would need to do some work on the
# # Haskell runtime to be able to generate new ones.
# try '(3 0)'
# try '(3 99)'
# try '(<isNat.seed> 0)'
# try '(<isNat.seed> 1)'
# try '(<cmp.seed> 0 1)'
# try '(<cmp.seed> 1 0)'
# try '(<cmp.seed> 1 1)'
# try '(<cmp.seed> (0 0) 1)'
# try '(<cmp.seed> (0 0) (1 1))'
# try '(<mul.seed> 3 4)'

MkPin="#0"
MkLaw="#1"
Inc="#2"
Case="#3"

Cnst="($MkPin ($MkLaw %Cnst 2 1))"
Cnst2="($MkPin ($MkLaw %Cnst2 3 1))"
Cnst3="($MkPin ($MkLaw %Cnst3 4 1))"

# NatCase z p x = Case (const z) (const3 z) (const2 z) z p x
NatCase="($MkPin ($MkLaw %NatCase 3 (0 (0 (0 (0 (0 (0 $Case (0 $Cnst 1)) (0 $Cnst3 1)) (0 $Cnst2 1)) 1) 2) 3)))"

# PlanCase p l a n x = Case p l a n (const n) x
PlanCase="($MkPin ($MkLaw %PlanCase 5 (0 (0 (0 (0 (0 (0 $Case 1) 2) 3) 4) (0 $Cnst 4)) 5)))"

Eqz="($MkPin ($MkLaw %Eqz 1 (0 (0 (0 (0 (0 (0 $Case (0 $Cnst (0 0))) (0 $Cnst3 (0 0))) (0 $Cnst2 (0 0))) (0 1)) (0 $Cnst (0 0))) 1)))"
If="($MkPin ($MkLaw %If 3 (0 (0 (0 $NatCase 2) (0 $Cnst 3)) (0 $Eqz 1))))"

id="($MkLaw 0 1 1)"
Dec="($MkPin ($MkLaw %Dec 1 (0 (0 ($NatCase (0 0)) $id) 1)))"
ToNat="($NatCase 0 $Inc)"
Times="($MkLaw %Times 3 (0 (0 (0 $NatCase 2) (0 (0 0 1) (0 1 2))) 3))"
Add="($MkPin ($MkLaw %Add 2 (0 (0 ($Times $Inc) (0 $ToNat 1)) 2)))"
Mul="($MkPin ($MkLaw %Mul 2 (0 (0 (0 $Times (0 $Add 1)) (0 0)) 2)))"
SubLaw="($MkLaw %Sub 2 (0 (0 ($Times $Dec) (0 $ToNat 1)) 2))"
Sub="($MkPin $SubLaw)"

# TODO fix Div, this is wrong
Div="($MkPin ($MkLaw %Div 2 1))"
# Div="($MkPin ($MkLaw %Div 2 (

# TODO fix Mod, this is wrong
Mod="($MkPin ($MkLaw %Mod 2 1))"

BaseDec="($Case 0 0 0 0 $id)"
DumbDec="($MkLaw %DumbDec 1 (0 ($Case 0 0 0 0 $id) 1))"

LawDec="($MkLaw %Dec 1 (0 (0 ($NatCase (0 0)) $id) 1))"

Ignore="($MkLaw 0 2 2)"
Trace="($MkPin ($MkLaw %Trace 2 2))" # this is a wrong defn of _Trace, as it doesn't force the first arg

# MapApp Map f h t = (Map f h) (f t)
MapApp="($MkLaw %MapApp 4 (0 (0 (0 1 2) 3) (0 2 4)))"

# Map f xs = PlanCase (const xs) (const3 xs) (MapApp Map f) xs xs
Map="($MkLaw %Map 2 (0 (0 (0 (0 (0 $PlanCase (0 $Cnst 2))
                                (0 $Cnst3 2))
                             (0 (0 $MapApp 0) 1))
                          2)
                       2))"

AppHead="($PlanCase 0 0 $Cnst 0)"
AppTail="($PlanCase 0 0 $Ignore 0)"

Inf1s="($MkLaw 99 1 (1 (0 1 2) 2) 1)"
# InfNats="($MkLaw 77 1 (0 (0 (0 $PlanCase (0 0))
#                             (0 0))
#                          (0 (

FAILED=0

check() {
  rm -r ./dot
  echo -n "TEST: $1 == [./plan] $2 ... "
  diff <(echo -e "$1") <(echo "$2" | ./plan)
  EXIT_CODE=$?
  if [[ $EXIT_CODE -eq 0 ]] ; then
    echo "PASSED"
  else
    FAILED=$((FAILED+1))
    echo "FAILED"
    sh/dotify # risky if many .dot files
    echo press ENTER once CPU usage backs off
    read
    feh -FB black -Z ./dot/*.png
    exit 1
  fi
}

echo "syntax"
check "3"     "3"
check "0"     "{}"
check "%a"    "{a}"
check "32123" "{{}}"

echo "primop inc"
check "3" "(#2 2)"
check "(3 4)" "(#2 2 4)"

echo "primop dec"
check "%z"     "(#3 7 7 7 %z 7 0)"
check "(%p 0)" "(#3 7 7 7 7 %p 1)"
check "(%p 1)" "(#3 7 7 7 7 %p 2)"

echo "basic"
check "5" "($Inc 4)"
check "1" "($Inc ($PlanCase 1 0 0 0 (4 9)))"

check "7" "($BaseDec 8)"
check "7" "($DumbDec 8)"
check "7" "($LawDec 8)"
check "7" "($Dec 8)"
check "8" "($MkLaw 1 2 ($Inc 7) 3 4)"
# check "{1 2 0}" "($MkLaw ($Inc 0) ($Inc ($Inc 0)) 0)"
# check "{1 2 0}" "(($MkLaw 1 2 0) 9 7)"
check "9" "(($MkLaw 1 2 1) 9 7)"
check "7" "(($MkLaw 1 2 2) 9 7)"
check "3" "(($MkLaw 1 2 3) 9 7)"
check "2" "($id ($id 2))"

echo "nat direct/big boundary"
check "9223372036854775810" "9223372036854775810"

echo "Eqz"
check "1" "($Eqz 0)"
check "0" "($Eqz 1)"
check "0" "($Eqz (0 0))"

echo "If"
check "7" "($If 5 7 9)"
check "9" "($If 0 7 9)"
check "(0 7)" "($If 6 (0 7) (0 9))"
check "(0 9)" "($If 0 (0 7) (0 9))"

echo "check sym bug"
check "(%fo %f)" "(%fo %f)"

echo "pins"
check "(<(0 1)> 2 3)" "(($MkPin (0 1)) 2 3)"
check "{1 2 0}" "(($MkPin 1) 1 2 0)"
check "{1 2 0}" "(($MkPin ($MkLaw 1)) 2 0)"
check "<{1 2 0}>" "(($MkPin ($MkLaw 1 2 0)) 3 4)"
check "<{1 2 0}>" "(($MkPin ($MkPin ($MkLaw 1 2 0))) 3 4)"

echo "let bindings"
check "9" "(($MkLaw 0 1 1) 9)"
check "9" "(($MkLaw 0 1 (1 1 2)) 9)"

echo "plan case"
check "(7 (4 5 6) 7)" "($PlanCase 7 7 7 7 (4 5 6 7))"

echo "symbols"
check "%foo" "7303014"
check "%goobar" "($Inc %foobar)"

check "%goobarfoobar" "(#2 %foobarfoobar)"

echo "complex law interp (calls)"
check "(777 888 3 4)"     "($MkLaw %ex 2 (0 (0 (0 1 2) 3) 4) 777 888)"
check "(777 (888 (3 4)))" "($MkLaw %ex 2 (0 1 (0 2 (0 3 4))) 777 888)"

echo "complex law interp (lets)"
check "4"     "($MkLaw %ex 2 (1 4 3)             777 888)"
check "(5 5)" "($MkLaw %ex 2 (1 4 (1 5 (0 3 4))) 777 888)"
check "(5 5)" "($MkLaw %ex 2 (1 5 (1 3 (0 3 4))) 777 888)"
check "(5 6)" "($MkLaw %ex 2 (1 5 (1 6 (0 3 4))) 777 888)"

check "((1 2 3) 5)" "(($MkLaw %foo 2) (1 (1 2 3) (1 4 (0 3 5))) 7 9)"

echo "nat arith"
check "3" "($ToNat 3)"
check "4" "($ToNat 4)"
check "0" "($ToNat 0)"
check "0" "($ToNat (0 0))"
check "0" "($id 0)"
check "4" "($id 4)"
check "8" "($Dec 9)"
check "900" "($Dec 901)"
check "7" "($Times $Inc 3 4)"
echo "Add"
check "2" "($Add 1 1)"
check "10" "($Add 4 6)"
check "(10 1)" "(($Add 4 6) 1)"
check "%n" "($Add 44 66)"
check "7" "($Add 4 ($Add 1 2))"
echo "Sub"
check "0"   "($SubLaw 0 0)"
check "0"   "($SubLaw 1 1)"
check "1"   "($SubLaw 1 0)"
check "0"   "($SubLaw 0 1)"
check "0"   "($SubLaw 4 6)"
check "8"   "($SubLaw 10 ($SubLaw 20 18))"
check "0"   "($Sub 0 0)"
check "0"   "($Sub 1 1)"
check "1"   "($Sub 1 0)"
check "0"   "($Sub 0 1)"
check "0"   "($Sub 4 6)"
check "22"  "($Sub 66 44)"
check "307" "($Sub 777 470)"
check "0"   "($Sub %a00000000 %zz00000000)"
check "8"   "($Sub 10 ($Sub 20 18))"
echo "Mul directs"
check "1" "($Mul 1 1)"
check "2" "($Mul 1 2)"
check "0" "($Mul 2 0)"
check "2" "($Mul 2 1)"
check "8" "($Mul 2 4)"
check "9" "($Mul 3 3)"
check "900" "($Mul 3 300)"
echo "Mul directs which overflow"
check "85070591730234615893513767968506380290" "($Mul 9223372036854775809 9223372036854775810)"
check "270350929966754336679420811073719260" "($Mul %chickens %turkeys)"
echo Mul BIG+direct
check "1090477602481288021329630" "($Mul %octocactus 2)"
check "1090477602481288021329630" "($Mul 2 %octocactus)"
echo Mul BIGs
check "1475887433180421662838272732634687279056224492909545382656893899996011391342627596" "($Mul %foooooooooooooooo %baaaaaaaaaaaaaaar)"

echo "Div directs"
check "1" "($Div 1 1)"
check "0" "($Div 1 2)"
check "0" "($Div 2 0)" # TODO
check "2" "($Div 2 1)"
check "2" "($Div 8 4)"
check "3" "($Div 9 3)"
check "300" "($Div 900 3)"
echo "Div big/direct"
check "9223372036854775809" "($Div 85070591730234615893513767968506380290 9223372036854775810)"
check "%chickens" "($Div 270350929966754336679420811073719260 %turkeys)"
echo "Div big/big -> direct"
check "2" "($Div 1090477602481288021329630 %octocactus)"
echo "Div big/big -> big"
check "%foooooooooooooooo" "($Div 1475887433180421662838272732634687279056224492909545382656893899996011391342627596 %baaaaaaaaaaaaaaar)"

echo "Mod directs"
check "0" "($Mod 1 1)"
check "1" "($Mod 1 2)"
check "0" "($Mod 2 0)" # TODO
check "0" "($Mod 2 1)"
check "0" "($Mod 8 4)"
check "0" "($Mod 9 3)"
check "3" "($Mod 11 8)"
check "21" "($Mod 917 64)"
echo "Mod big/direct"
check "0" "($Mod 85070591730234615893513767968506380290 9223372036854775810)"
check "100000" "($Mod 85070591730234615893513767968506480290 9223372036854775810)"
check "0" "($Mod 270350929966754336679420811073719260 %turkeys)"
check "22503098823046516" "($Mod 270350929966754336669420811073719260 %turkeys)"
echo "Mod big/big -> direct"
check "0" "($Mod 1090477602481288021329630 %octocactus)"
check "545238801230644010664815" "($Mod 1090477602471288021329630 %octocactus)"
echo "Mod big/big -> big"
check "22574545732039792372647150078446771890150" "($Mod 14758874331804216628382727326346872790562244929095453826568938999601391342627596 %baaaaaaaaaaaaaaar)"

echo "cnst/ignore"
check "11" "($Cnst 11 7)"
check "7"  "($Ignore 11 7)"
check "13" "($Cnst3 13 1 4 7)"

echo "Trace"
check "0\n1" "($Trace 0 1)"
check "2\n0" "($Trace ($Add 1 1) 0)"
check "(0 1 2 3 4)\n1" "($Trace (0 1 2 3 4) 1)"

echo "map"
check "(0 9999 10000 10001 10003 10004)" "($Map ($Add 9999) (0 0 1 2 4 5))"

echo "infinite values"
check "1" "($AppHead $Inf1s)"

echo "refer to later binder from an earlier one"
check "7" "($MkLaw 0 1 (1 3 (1 7 2)) 9)"

echo "refer to earlier binder from a later one"
check "7" "($MkLaw 0 1 (1 7 (1 2 3)) 9)"

echo "more complex example"
check "(1 (0 2))" "($MkLaw 0 1 (1 (0 (0 0) 3) (1 (0 2) (0 1 2))) 1)"

echo "trivial cycles are okay if not used"
check "7" "($MkLaw 0 1 (1 7 (1 3 2)) 9)"

echo "moderate-length symbols"
check "%fooooooooooooooooooooooooooo" "%fooooooooooooooooooooooooooo"

echo "incr smol sym"
check "%gooooooooooooooooooooooo" "($Inc ($PlanCase 0 0 $Cnst 0 (%fooooooooooooooooooooooo %f)))"
check "%g" "($Inc ($PlanCase 0 0 $Ignore 0 (%fooooooooooooooooooooooo %f)))"

echo "large atoms"
check "%foooooooooooooooo" "37919465640883872069706873901102452928358"
check "75838931281767744139413747802204905856717" "($Add 37919465640883872069706873901102452928358 37919465640883872069706873901102452928359)"

VAL=$(printf '%%%*s\n' "2000" | tr ' ' "a")
diff <(echo "$VAL") <(echo "$VAL" | ./plan)
EXIT_CODE=$?
if [[ $EXIT_CODE -ne 0 ]] ; then
  echo "large symbol test FAILED";
  FAILED=$((FAILED+1))
else
  echo "large symbol test PASSED";
fi

echo "seed tests"
check "1" "(<Sub> 2 1)"
check "6" "(<Mul> 2 3)"
check "0" "(<Cmp> 0 2)"
check "1" "(<Cmp> 2 2)"
check "2" "(<Cmp> 4 2)"

check "2" "(<Cmp> #2 2)"
check "1" "(<Cmp> #2 #2)"
check "0" "(<Cmp> #2 (0 1))"

check "(0 7 7 1 2 7 7)" "(<Splice> 2 (0 1 2) (0 7 7 7 7))"

check "1" "(<strFindIndexOff> (<Neq> 32) 0 { x y })"
check "1" "(<strFindIndexOff> (<Neq> 32) 1 { x y })"
check "3" "(<strFindIndexOff> (<Neq> 32) 2 { x y })"
check "3" "(<strFindIndexOff> (<Neq> 32) 3 { x y })"
check "5" "(<strFindIndexOff> (<Neq> 32) 4 { x y })"
check "5" "(<strFindIndexOff> (<Neq> 32) 5 { x y })"
check "5" "(<strFindIndexOff> (<Neq> 32) 6 { x y })"

check "(0 (0 %fn 1 %x) 0 1 %LWORD)"        "(<lexerTest> %x)"
check "(0 (0 %fn 1 544897400) 0 3 %LWORD)" "(<lexerTest> {xyz })"

check \
  "(0 (0 %REPL 3 %WOODS) (0 (0 1 (%OPEN <%rex> 61 (0 (%NEST <%rex> 124 (0 (%WORD <%rex> %Pin 0) (%WORD <%rex> %i 0)) 0) 0) (%OPEN <%rex> 61 (0 (%NEST <%rex> 124 (0 (%WORD <%rex> %Inc 0) (%WORD <%rex> %m 0)) 0) 0) 0)))))" \
  "(<rexTrial> (0 {= (Pin i) | ##0 i} {= (Inc m) | ##2 m}))"

check '(0 (%A (%K <2>) (%K 3)))' \
      '(<sireTrial> (0 {| ##2} {| 3}))'



################################################################################

echo 'Parsing Rex (slow)'

time ./plan <<EOF
(<rexTrial>
 (0 {= (Pin i)            | ##0 i}
    {= (Law n a b)        | ##1 n a b}
    {= (Inc m)            | ##2 m}
    {= (Case p l a z m o) | ##3 p l a z m o}
    {= (Die x)            | ##die x  ; Calling a primop above 3 is a crash.}))
EOF

################################################################################

if [[ "$FAILED" -eq 0 ]]; then
  echo "all tests passed!"
elif [[ "$FAILED" -eq 1 ]]; then
  echo "1 test failed"
else
  echo "$FAILED tests failed"
fi
exit $FAILED;
