(set-logic AUFLIA)

(declare-fun inhabitant (Int) Int)
(declare-fun has_type (Int) Int)

; P = { 
;   sigma0 -> @(@(c1, sigma1), sigma2);
;   sigma1 -> c2;
;   sigma2 -> @(c3, sigma3);
;   sigma3 -> c4;
;   sigma3 -> @(c5, sigma0);
; }

(define-fun grammar () Bool
  (forall ((i Int))      
    (=> (not (< i 0))
      (and
;        (and 
;          (< (has_type i) 4)
;          (> (has_type i) -2)
;          (< (inhabitant i) 6)
;          (> (inhabitant i) -2)
;        )
        (=
          (= (has_type i) 0)
          (and (= (inhabitant i) 0)
            (= (inhabitant (+ i i)) 0)
            (= (inhabitant (+ i i i i)) 1)
            (= (has_type (+ i i i i 1)) 1)
            (= (has_type (+ i i 1)) 2))
        )
        (=
          (= (has_type i) 1)
          (= (inhabitant i) 2)
        )
        (=
          (= (has_type i) 2)
          (and (= (inhabitant i) 0)
            (= (inhabitant (+ i i)) 3)
            (= (has_type (+ i i 1)) 3))
        )
        (=
         (= (has_type i) 3)
         (xor (= (inhabitant i) 4)
              (and (= (inhabitant i) 0)
                (= (inhabitant (+ i i)) 5)
                (= (has_type (+ i i 1)) 0)))
         
        )
      )
  )))
(define-fun grammar2 () Bool
  (forall ((i Int))      
      (=> (not (< i 0))
        (and
          (=>
            (= (has_type i) 0)
            (and (= (inhabitant i) 0)
              (= (inhabitant (+ i i)) 2)
              (= (has_type (+ i i 1)) 1))
          )
          (=>
            (= (has_type i) 1)
            (= (inhabitant i) 3)
          )
        ))
))


(declare-const i1 Int)
(declare-const i2 Int)
(declare-const i3 Int)
(declare-const i4 Int)
(declare-const i5 Int)
(declare-const i6 Int)
(declare-const i7 Int)
(declare-const i8 Int)
(declare-const i9 Int)
(declare-const i10 Int)
(declare-const i11 Int)
(declare-const i12 Int)
(declare-const i13 Int)
(declare-const i14 Int)
(declare-const i15 Int)

(assert (and 
  (= (has_type 1) 0) 
  grammar
  (= i1 (inhabitant 1))
  (= i2 (inhabitant 2))
  (= i3 (inhabitant 3))
  (= i4 (inhabitant 4))
  (= i5 (inhabitant 5))
  (= i6 (inhabitant 6))
  (= i7 (inhabitant 7))
  (= i8 (inhabitant 8))
  (= i9 (inhabitant 9))
  (= i10 (inhabitant 10))
  (= i11 (inhabitant 11))
  (= i12 (inhabitant 12))
  (= i13 (inhabitant 13))
  (= i14 (inhabitant 14))
  (= i15 (inhabitant 15))
))
                      
(check-sat)
(get-model)

