=Pin  #0
=Law  #1
=Inc  #2
=Case #3

=k  (Pin (Law %k  2 1))
=k2 (Pin (Law %k2 3 1))
=k3 (Pin (Law %k3 4 1))

=A   0
=K   0
=LET 1

; NatCase z p x = Case (const z) (const3 z) (const2 z) z p x
=NatCase
 (Pin
  (Law %NatCase 3
   (A (A (A (A (A (A Case (A k 1)) (A k3 1)) (A k2 1)) 1) 2) 3)))

; PlanCase p l a n x = Case p l a n (const n) x
=PlanCase
 (Pin
  (Law %PlanCase 5
   (A (A (A (A (A (A Case 1) 2) 3) 4) (A k 4)) 5)))

; Eqz x = (Case (k 0) (K3 0) (k2 0) 1 (k 0)
=Eqz
 (Pin
  (Law %Eqz 1
   (A (A (A (A (A (A Case (k 0)) (k3 0)) (k2 0)) (K 1)) (A k (K 0))) 1)))

; If c t e = (NatCase t (k e) (Eqz 1))
=If
 (Pin
  (Law %If 3
   (A (A (A NatCase 2) (A k 3)) (A Eqz 1))))

=id (Law 0 1 1)

=Dec (Pin (Law %Dec 1 (0 (0 (NatCase (K 0)) id) 1)))

=ToNat (NatCase 0 Inc)

=Times  (Law %Times 3 (0 (0 (0 NatCase 2) (0 (0 0 1) (0 1 2))) 3))
=Add    (Pin (Law %Add 2 (0 (0 (Times Inc) (0 ToNat 1)) 2)))
=Mul    (Pin (Law %Mul 2 (0 (0 (0 Times (0 Add 1)) (0 0)) 2)))
=SubLaw (Law %Sub 2 (0 (0 (Times Dec) (0 ToNat 1)) 2))
=Sub    (Pin SubLaw)
=Pow    (Pin (Law %Pow 2 (0 (0 (0 Times (0 Mul 1)) (K 1)) 2)))
=Bex    (Pin (Law %Bex 1 (0 (Pow 2) 1)))

; TODO fix Div, this is wrong
=Div (Pin (Law %Div 2 1))
; Div=(Pin (Law %Div 2 ()))

; TODO fix Mod, this is wrong
=Mod (Pin (Law %Mod 2 1))

=BaseDec (Case 0 0 0 0 id)
=DumbDec (Law %DumbDec 1 (0 (Case 0 0 0 0 id) 1))
=LawDec  (Law %Dec 1 (0 (0 (NatCase (0 0)) id) 1))

=Ignore (Law 0 2 2)
=Trace  (Pin (Law %Trace 2 2))
; this is a wrong defn of _Trace, as it doesn't force the first arg

; MapApp Map f h t = (Map f h) (f t)
=MapApp (Law %MapApp 4 (0 (0 (0 1 2) 3) (0 2 4)))

; Map f xs = PlanCase (const xs) (const3 xs) (MapApp Map f) xs xs
=Map (Law %Map 2
      (0 (0 (0 (0 (0 PlanCase (0 k 2))
                (0 k3 2))
             (0 (0 MapApp 0) 1))
          2)
       2))

=AppHead (PlanCase 0 0 k 0)
=AppTail (PlanCase 0 0 Ignore 0)

=Inf1s (Law 99 1 (1 (0 1 2) 2) 1)


; nats n = n : nats (n+1)
; nats n = (0 n (nats (inc n)))
=Nats (Law %Nats 1 (A (A (K 0) 1) (A 0 (0 #2 1))))

{syntax}

! 3        3
! 0        {}
! %a       {a}
! 32123    {{}}
! (%fo %f) (%fo %f)

=x 1 =y 3 ! (1 2 3) (x 2 y)

{primop inc}

! 3     (#2 2)
! (3 4) (#2 2 4)

{primop dec}

! %z     (#3 7 7 7 %z 7 0)
! (%p 0) (#3 7 7 7 7 %p 1)
! (%p 1) (#3 7 7 7 7 %p 2)

{basic}

! 5 (Inc 4)
! 1 (Inc (PlanCase 1 0 0 0 (4 9)))

! 7           (BaseDec 8)
! 7           (DumbDec 8)
! 7           (LawDec 8)
! 7           (Dec 8)
! 8           (Law 1 2 (Inc 7) 3 4)
! (Law 1 2 0) (Law (Inc 0) (Inc (Inc 0)) 0)
! (Law 1 2 0) ((Law 1 2 0) 9 7)
! 9           ((Law 1 2 1) 9 7)
! 7           ((Law 1 2 2) 9 7)
! 3           ((Law 1 2 3) 9 7)
! 2           (id (id 2))

{nat direct/big boundary}

! 9223372036854775810 9223372036854775810

{Eqz}

! 1 (Eqz 0)
! 0 (Eqz 1)
! 0 (Eqz (0 0))

{If}

! 7     (If 5 7 9)
! 9     (If 0 7 9)
! (0 7) (If 6 (0 7) (0 9))
! (0 9) (If 0 (0 7) (0 9))

{pins}

! ((Pin (0 1)) 2 3) ((Pin (0 1)) 2 3)
! (Law 1 2 0)       ((Pin 1) 1 2 0)
! (Law 1 2 0)       ((Pin (Law 1)) 2 0)
! (Pin (Law 1 2 0)) ((Pin (Law 1 2 0)) 3 4)
! (Pin (Law 1 2 0)) ((Pin (Pin (Law 1 2 0))) 3 4)

{let bindings}

! 9 ((Law 0 1 1) 9)
! 9 ((Law 0 1 (1 1 2)) 9)

{plan case}

! (7 (4 5 6) 7) (PlanCase 7 7 7 7 (4 5 6 7))

{symbols}

! %foo 7303014
! %goobar (Inc %foobar)

! %goobarfoobar (#2 %foobarfoobar)

{complex law interp (calls)}

! (777 888 3 4)     (Law %ex 2 (0 (0 (0 1 2) 3) 4) 777 888)
! (777 (888 (3 4))) (Law %ex 2 (0 1 (0 2 (0 3 4))) 777 888)

{complex law interp (lets)}

! 4     (Law %ex 2 (1 4 3)             777 888)
! (5 5) (Law %ex 2 (1 4 (1 5 (0 3 4))) 777 888)
! (5 5) (Law %ex 2 (1 5 (1 3 (0 3 4))) 777 888)
! (5 6) (Law %ex 2 (1 5 (1 6 (0 3 4))) 777 888)

! (1 2 3 5)
  ((Law %foo 2) (1 (1 2 3) (1 4 (0 3 5))) 7 9)

{nat arith}

! 3   (ToNat 3)
! 4   (ToNat 4)
! 0   (ToNat 0)
! 0   (ToNat (0 0))
! 0   (id 0)
! 4   (id 4)
! 8   (Dec 9)
! 900 (Dec 901)
! 7   (Times Inc 3 4)

{Add}

! 2      (Add 1 1)
! 10     (Add 4 6)
! (10 1) ((Add 4 6) 1)
! %n     (Add 44 66)
! 7      (Add 4 (Add 1 2))

{Sub}

! 0   (SubLaw 0 0)
! 0   (SubLaw 1 1)
! 1   (SubLaw 1 0)
! 0   (SubLaw 0 1)
! 0   (SubLaw 4 6)
! 8   (SubLaw 10 (SubLaw 20 18))
! 0   (Sub 0 0)
! 0   (Sub 1 1)
! 1   (Sub 1 0)
! 0   (Sub 0 1)
! 0   (Sub 4 6)
! 22  (Sub 66 44)
! 307 (Sub 777 470)
! 0   (Sub %a00000000 %zz00000000)
! 8   (Sub 10 (Sub 20 18))

{Mul directs}

! 1   (Mul 1 1)
! 2   (Mul 1 2)
! 0   (Mul 2 0)
! 2   (Mul 2 1)
! 8   (Mul 2 4)
! 9   (Mul 3 3)
! 900 (Mul 3 300)

{Mul directs which overflow}

! 85070591730234615893513767968506380290
  (Mul 9223372036854775809 9223372036854775810)

! 270350929966754336679420811073719260
  (Mul %chickens %turkeys)

{Mul BIG+direct}

! 1090477602481288021329630 (Mul %octocactus 2)
! 1090477602481288021329630 (Mul 2 %octocactus)

{Mul BIGs}

! 1475887433180421662838272732634687279056224492909545382656893899996011391342627596
  (Mul %foooooooooooooooo %baaaaaaaaaaaaaaar)

{Binary Exponent}

! 4294967296           (Bex 32)
! 9223372036854775808  (Bex 63)
! 18446744073709551616 (Mul 2 9223372036854775808)
! 18446744073709551616 (Bex 64)

{Div directs}

! 1   (Div 1 1)
! 0   (Div 1 2)
! 2   (Div 2 1)
! 2   (Div 8 4)
! 3   (Div 9 3)
! 300 (Div 900 3)

{Div big/direct}

! 9223372036854775809
  (Div 85070591730234615893513767968506380290 9223372036854775810)

! %chickens
  (Div 270350929966754336679420811073719260 %turkeys)

{Div big/big -> direct}

! 2 (Div 1090477602481288021329630 %octocactus)

{Div big/big -> big}

! %foooooooooooooooo
 (Div
  1475887433180421662838272732634687279056224492909545382656893899996011391342627596
  %baaaaaaaaaaaaaaar)

{Mod directs}

! 0  (Mod 1 1)
! 1  (Mod 1 2)
! 0  (Mod 2 1)
! 0  (Mod 8 4)
! 0  (Mod 9 3)
! 3  (Mod 11 8)
! 21 (Mod 917 64)

{Mod big/direct}

! 0 (Mod 85070591730234615893513767968506380290 9223372036854775810)
! 100000 (Mod 85070591730234615893513767968506480290 9223372036854775810)
! 0 (Mod 270350929966754336679420811073719260 %turkeys)
! 22503098823046516 (Mod 270350929966754336669420811073719260 %turkeys)

{Mod big/big -> direct}

! 0 (Mod 1090477602481288021329630 %octocactus)
! 545238801230644010664815 (Mod 1090477602471288021329630 %octocactus)

{Mod big/big -> big}

! 22574545732039792372647150078446771890150 (Mod 14758874331804216628382727326346872790562244929095453826568938999601391342627596 %baaaaaaaaaaaaaaar)

{cnst/ignore}

! 11 (k 11 7)
! 7  (Ignore 11 7)
! 13 (k3 13 1 4 7)

{Trace}

! 1 (Trace 0 1)
! 0 (Trace (Add 1 1) 0)
! 1 (Trace (0 1 2 3 4) 1)

{map}

! (0 9999 10000 10001 10003 10004)
  (Map (Add 9999) (0 0 1 2 4 5))

{infinite values}

! 1 (AppHead Inf1s)

{refer to later binder from an earlier one}

! 7 (Law 0 1 (1 3 (1 7 2)) 9)

{refer to earlier binder from a later one}

! 7 (Law 0 1 (1 7 (1 2 3)) 9)

{more complex example}

! (1 (0 2)) (Law 0 1 (1 (0 (0 0) 3) (1 (0 2) (0 1 2))) 1)

{trivial cycles are okay if not used}

! 7 (Law 0 1 (1 7 (1 3 2)) 9)

{moderate-length symbols}

! %fooooooooooooooooooooooooooo %fooooooooooooooooooooooooooo

{incr smol sym}

! %gooooooooooooooooooooooo
  (Inc (PlanCase 0 0 k 0 (%fooooooooooooooooooooooo %f)))

! %g
  (Inc (PlanCase 0 0 Ignore 0 (%fooooooooooooooooooooooo %f)))

{large atoms}

! %foooooooooooooooo
  37919465640883872069706873901102452928358

! 75838931281767744139413747802204905856717
  (Add 37919465640883872069706873901102452928358
       37919465640883872069706873901102452928359)

! 1 (@Sub 2 1)
! 6 (@Mul 2 3)
! 0 (@Cmp 0 2)
! 1 (@Cmp 2 2)
! 2 (@Cmp 4 2)

! 2 (@Cmp #2 2)
! 1 (@Cmp #2 #2)
! 0 (@Cmp #2 (0 1))
! 2 (@Cmp 5 0)
! 1 (@Cmp 5 5)
! 1 (@Cmp #5 #5)
! 0 (@Cmp #0 #5)
! 2 (@Cmp #5 #0)
! 2 (@Cmp (#1 2 3 4) #0)
! 2 (@Cmp (#1 2 3 4) #1)
! 0 (@Cmp (#1 2 3 4) (0 1))
! 1 (@Cmp (#1 2 3 4) (#1 2 3 4))
! 2 (@Cmp (#1 2 3 4) (#1 2 3 3))
! 2 (@Cmp (#1 2 4 4) (#1 2 3 3))
! 2 (@Cmp (#1 2 4 4) (#1 2 3 5))
! 0 (@Cmp (#1 2 3 4) (#1 2 3 5))
! 2 (@Cmp (#1 2 3 4) (#1 0 3 5))
! 0 (@Cmp (#1 0 3 4) (#1 0 3 5))
! 2 (@Cmp (#1 1 3 4) (#1 0 3 5))
! 2 (@Cmp (#1 1 3 4) (#1 0 3 5))

; 0 (@Cmp (0 (#7 7)) (1 (#7 7)))

! (0 7 7 1 2 7 7) (@Splice 2 (0 1 2) (0 7 7 7 7))

! 1 (@strFindIndexOff (@Neq 32) 0 { x y })
! 1 (@strFindIndexOff (@Neq 32) 1 { x y })
! 3 (@strFindIndexOff (@Neq 32) 2 { x y })
! 3 (@strFindIndexOff (@Neq 32) 3 { x y })
! 5 (@strFindIndexOff (@Neq 32) 4 { x y })
! 5 (@strFindIndexOff (@Neq 32) 5 { x y })
! 5 (@strFindIndexOff (@Neq 32) 6 { x y })

! (0 (0 %fn 1 %x) 0 1 %LWORD)        (@lexerTest %x)
! (0 (0 %fn 1 544897400) 0 3 %LWORD) (@lexerTest {xyz })

! (0
   (0 %REPL 2 %WOODS)
   (0
    (0 1 (%OPEN #rex 61 (0 (%NEST #rex 124 (0 (%WORD #rex %Pin 0)
                                              (%WORD #rex %i 0))
                            0)
                         0)
          0))))
  (@rexTrial
   (0 {= (Pin i)            | ##0 i}))

(@rexTrial
 (0 {= (Pin i)            | ##0 i}
    {= (Law n a b)        | ##1 n a b}
    {= (Inc m)            | ##2 m}
    {= (Case p l a z m o) | ##3 p l a z m o}
    {= (Die x)            | ##die x  ; Calling a primop above 3 is a crash.}
 ))

! (0 (%A (%K #2) (%K 3)))
  (@sireTrial (0 {| ##2} {| 3}))

! (0 (%F (0 1 0 0 %Pin 1 (%K 0))))
  (@sireTrial (0 {?? (Pin i)            | ##0 i}))

; (WORD n)=(%WORD #rex n 0)
=WORD (Pin (Law %WORD 1) (A (A (%WORD #rex) 1) (K 0)))

! ; TODO the structure is correct, but the word-data from words deeper
  ; into the line are zero'd out.  This must be a problem with ByteSlice
  ; or similar.

  (@rexTrial
   (0 {?? (Case p l a z m o)}
      { | ##3 p l a z m o}))

  (0 (0 %REPL 3 %WOODS)
    (0 (0 1 (%OPEN #rex {??}
               (0 (%NEST #rex {|} (0 (WORD {Case})
                                     (WORD 0)
                                     (WORD 0)
                                     (WORD 0)
                                     (WORD 0)
                                     (WORD 0)
                                     (WORD 0))
                   0))
             (%OPEN #rex {|}
                (0 (%PREF #rex {##} (0 (WORD {3})) 0)
                   (WORD %p)
                   (WORD 0)
                   (WORD 0)
                   (WORD 0)
                   (WORD 0)
                   (WORD 0))
              0)))))

; TODO: This crashes, probably because the above parsing logic is wrong.
(@sireTrial
  (0
   {= Car}
   {@ Case}
   {  ?? (Case p l a z m o)}
   {   | ##3 p l a z m o}
   {@ PlanCase}
   {   ?? (PlanCase p l a n x)}
   {    | Case p l a n _&n x}
   {@ Car}
   {   ?? (Car x)}
   {    | PlanCase _&(##0) (n a _)&(##1 n a) (h _)&h 0 x}
   {Car}
))
