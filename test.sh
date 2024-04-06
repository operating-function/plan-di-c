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
NatCase="#3"
PlanCase="#4"

id="($MkLaw 0 1 1)"
Dec="($NatCase 0 $id)"
ToNat="($NatCase 0 $Inc)"
Times="($MkLaw 126879464510559 3 (0 (0 (0 (2 $NatCase) 2) (0 (0 0 1) (0 1 2))) 3))"
Add="($MkLaw 1684291935 2 (0 (0 ($Times $Inc) (0 $ToNat 1)) 2))"
Mul="($MkLaw 99 2 (0 (0 (0 $Times (0 $Add 1)) (2 0)) 2))"

Cnst="($MkLaw 0 2 1)"
Cnst3="($MkLaw 0 4 1)"
Ignore="($MkLaw 0 2 2)"

MapApp="($MkLaw 0 4 (0 (0 (0 1 2) 3) (0 2 4)))"
Map="($MkLaw 0 2 (0 (0 (0 (0 (0 $PlanCase (0 $Cnst 2))
                             (0 $Cnst3 2))
                          (0 (0 $MapApp 0) 1))
                       (0 $Cnst 2))
                    2))"

AppHead="($PlanCase 0 0 $Cnst 0)"
AppTail="($PlanCase 0 0 $Ignore 0)"

Inf1s="($MkLaw 99 1 (1 (0 1 2) 2) 1)"
# InfNats="($MkLaw 77 1 (0 (0 (0 $PlanCase (2 0))
#                             (2 0))
#                          (0 (

FAILED=0

check() {
  echo -n "TEST: $1 == [./plan] $2 ... "
  diff <(echo $1) <(echo $2 | ./plan)
  EXIT_CODE=$?
  if [[ $EXIT_CODE -eq 0 ]] ; then
    echo "PASSED"
  else
    FAILED=1
    echo "FAILED"
  fi
}

echo "basic"
check "5" "($Inc 4)"
check "1" "($Inc ($PlanCase 1 0 0 0 (4 9)))"
check "8" "(($MkLaw 1 2 (2 ($Inc 7))) 3 4)"
check "{1 2 0}" "(($MkLaw 1 2 0) 9 7)"
check "9" "(($MkLaw 1 2 1) 9 7)"
check "7" "(($MkLaw 1 2 2) 9 7)"
check "3" "(($MkLaw 1 2 3) 9 7)"

echo "pins"
check "(<(0 1)> 2 3)" "(($MkPin (0 1)) 2 3)"
check "{1 2 0}" "(($MkPin 1) 1 2 0)"
check "{1 2 0}" "(($MkPin ($MkLaw 1)) 2 0)"
check "<{1 2 0}>" "(($MkPin ($MkLaw 1 2 0)) 3 4)"
check "<{1 2 0}>" "(($MkPin ($MkPin ($MkLaw 1 2 0))) 3 4)"

echo "let bindings"
check "9" "(($MkLaw 0 1 1) 9)"
check "9" "(($MkLaw 0 1 (1 1 2)) 9)"

echo "refer to later binder from an earlier one"
check "9" "(($MkLaw 0 1 (1 3 (1 9 2))) 9)"

echo "more complex example"
check "(1 (0 2))" "($MkLaw 0 1 (1 (0 (2 0) 3) (1 (2 2) (0 1 2))) 1)"

echo "trivial cycles are okay if not used"
check "7" "($MkLaw 0 1 (1 7 (1 3 2)) 9)"
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
check "10" "($Add 4 6)"
check "%d" "($Times $Inc 41 59)"
check "44" "($Mul 4 11)"
check "49" "($Mul 7 7)"

echo "cnst/ignore"
check "11" "($Cnst 11 7)"
check "7"  "($Ignore 11 7)"
check "13" "($Cnst3 13 1 4 7)"

echo "map"
check "(0 9999 10000 10001 10003 10004)" "($Map ($Add 9999) (0 0 1 2 4 5))"

echo "infinite values"
check "1" "($AppHead $Inf1s)"

echo "moderate-length symbols"
check "%fooooooooooooooooooooooooooo" "%fooooooooooooooooooooooooooo"

echo "large atoms TODO"
check "%foooooooooooooooo" "37919465640883872069706873901102452928358"

VAL=$(printf '%%%*s\n' "2000" | tr ' ' "a")
diff <(echo "$VAL") <(echo "$VAL" | ./plan)
EXIT_CODE=$?
if [[ $EXIT_CODE -ne 0 ]] ; then
  echo "large symbol FAILED";
  FAILED=1;
else
  echo "large symbol PASSED";
fi

exit $FAILED;
