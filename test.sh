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

Cnst="($MkPin ($MkLaw 0 2 1))"
Cnst2="($MkPin ($MkLaw 0 3 1))"
Cnst3="($MkPin ($MkLaw 0 4 1))"

# NatCase z p x = Case (const z) (const3 z) (const2 z) z p x
NatCase="($MkPin ($MkLaw %NatCase 3 (0 (0 (0 (0 (0 (0 $Case (0 $Cnst 1)) (0 $Cnst3 1)) (0 $Cnst2 1)) 1) 2) 3)))"

# PlanCase p l a n x = Case p l a n (const n) x
PlanCase="($MkPin ($MkLaw %PlanCase 5 (0 (0 (0 (0 (0 (0 $Case 1) 2) 3) 4) (0 $Cnst 4)) 5)))"

id="($MkLaw 0 1 1)"
Dec="($MkPin ($MkLaw %Dec 1 (0 (0 ($NatCase (0 0)) $id) 1)))"
ToNat="($NatCase 0 $Inc)"
Times="($MkLaw %Times 3 (0 (0 (0 $NatCase 2) (0 (0 0 1) (0 1 2))) 3))"
Add="($MkPin ($MkLaw %Add 2 (0 (0 ($Times $Inc) (0 $ToNat 1)) 2)))"
Mul="($MkPin ($MkLaw %Mul 2 (0 (0 (0 $Times ($Add 1)) (0 0)) 2)))"
Sub="($MkPin ($MkLaw %Sub 2 (0 (0 ($Times $Dec) (0 $ToNat 1)) 2)))"

Ignore="($MkLaw 0 2 2)"
Trace="($MkPin ($MkLaw %Trace 2 2))" # this is a wrong defn of _Trace, as it doesn't force the first arg

MapApp="($MkLaw 0 4 (0 (0 (0 1 2) 3) (0 2 4)))"
Map="($MkLaw 0 2 (0 (0 (0 (0 (0 $PlanCase (0 $Cnst 2))
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
  echo -n "TEST: $1 == [./plan] $2 ... "
  diff <(echo -e "$1") <(echo "$2" | ./plan)
  EXIT_CODE=$?
  if [[ $EXIT_CODE -eq 0 ]] ; then
    echo "PASSED"
  else
    FAILED=$((FAILED+1))
    echo "FAILED"
  fi
}

echo "basic"
check "5" "($Inc 4)"
check "1" "($Inc ($PlanCase 1 0 0 0 (4 9)))"
check "7" "($Dec 8)"
check "8" "($MkLaw 1 2 ($Inc 7) 3 4)"
check "{1 2 0}" "($MkLaw ($Inc 0) ($Inc ($Inc 0)) 0)"
check "{1 2 0}" "(($MkLaw 1 2 0) 9 7)"
check "9" "(($MkLaw 1 2 1) 9 7)"
check "7" "(($MkLaw 1 2 2) 9 7)"
check "3" "(($MkLaw 1 2 3) 9 7)"
check "2" "($id ($id 2))"

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
check "10" "($Add 4 6)"
check "(10 1)" "(($Add 4 6) 1)"
check "%n" "($Add 44 66)"
check "7" "($Add 4 ($Add 1 2))"
echo "Sub"
check "2" "($Sub 6 4)"
check "0" "($Sub 4 6)"
check "22" "($Sub 66 44)"
check "307" "($Sub 777 470)"
check "8" "($Sub 10 ($Sub 20 18))"
echo "Mul ptr-nats"
check "8" "($Mul 2 4)"
check "9" "($Mul 3 3)"
check "900" "($Mul 3 300)"
echo "Mul heap SMALLs"
check "85070591730234615893513767968506380290" "($Mul 9223372036854775809 9223372036854775810)"
echo Mul BIGs
check "4337243350382979986872112349518590392945420" "($Mul %foooooooo %baaaaaaar)"
check "1475887433180421662838272732634687279056224492909545382656893899996011391342627596" "($Mul %foooooooooooooooo %baaaaaaaaaaaaaaar)"

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

if [[ "$FAILED" -eq 0 ]]; then
  echo "all tests passed!"
elif [[ "$FAILED" -eq 1 ]]; then
  echo "1 test failed"
else
  echo "$FAILED tests failed"
fi
exit $FAILED;
