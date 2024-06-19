module DependentProofs

import Data.Vect

%default total


-- Experimented with dependent types for mathematical proofs.
-- Here are some basic arithmetic operations, but also complex data structure manipulations, decidable logic.


-- Proof of addition with successor
plus_one_right : {n : Nat} -> n + 1 = S n
plus_one_right {n = 0} = Refl
plus_one_right {n = (S n)} = cong S plus_one_right


-- Vector reverse function
vect_reverse : {n : Nat} -> Vect n a -> Vect n a
vect_reverse {n = Z} xs = []
vect_reverse {n = (S k)} (x :: xs) = rec (vect_reverse xs) x
    where
        rec : Vect n a -> a -> Vect (S n) a
        rec [] y = [y]
        rec (x :: xs) y = x :: rec xs y


-- Decidable logic for conjunction and negation
data And : (p : Type) -> (q : Type) -> Type where
  Both : (prf_of_p : p) -> (prf_of_q : q) -> And p q

dec_and : Dec p -> Dec q -> Dec (p `And` q)
dec_and (Yes prf_p) (Yes prf_q) = Yes (Both prf_p prf_q)
dec_and (Yes prf) (No contr_q) = No (\op => case op of
                        (Both prf_p prf_q) => contr_q prf_q)
dec_and (No contr_p) (Yes prf) = No (\op => case op of
                        (Both prf_p prf_q) => contr_p prf_p)
dec_and (No contr_p) (No contr_q) = No (\op => case op of
                        (Both prf_p prf_q) => contr_p prf_p) 

dec_not : Dec p -> Dec (Not p)
dec_not (Yes prf) = No (\x => x prf)
dec_not (No contra) = Yes contra


-- Even number proof and halving function
data  IsEven : (n : Nat) -> Type  where
	IsEvenZ  :  IsEven 0
	IsEvenSS :  IsEven n -> IsEven (S (S n))

half : (n : Nat) -> (is_even : IsEven n) => Nat
half 0 = 0
half (S (S k)) = case (is_even) of
                    (IsEvenSS x) => 1 + half (k)


-- Resource management and conditional update logic
record PlayerState where
    constructor PS
    health : Fin 11
    wealth : Fin 101

hire_healer : PlayerState -> PlayerState
hire_healer (PS health wealth) = if wealth >= 10 
        then (if health < 10 then PS (health + 1) (wealth - 10) else PS health wealth)
        else PS health wealth

psToStr : PlayerState -> String
psToStr (PS health wealth) = show health ++ " " ++ show wealth
-- > psToStr (hire_healer (PS 1 100))
-- > psToStr (hire_healer (PS 10 50))
-- > psToStr (hire_healer (PS 1 9))


-- Complex number arithmetic implementation
record  Complex where
	constructor  (!!)
	real :  Double
	imaginary  :  Double

infix 6 !!

implementation Num Complex where
  (a !! bi) + (c !! di) = (a + c) !! (bi + di)
  (a !! bi) * (c !! di) = (a * c - bi * di) !! (a * di + bi * c)
  fromInteger x = (fromInteger x) !! 0

-- > (1 !! 2) + (3 !! 4)
-- > (1 !! 2) * (3 !! 4)
-- > the Complex (fromInteger 7)




