module Proofs

import Data.List
import Data.Vect
import Data.Fin

%default total


-- Did some Idris2 experiments with proofs and properties in dependent type theory, such like the sorted lists, logical connectives, quantifiers, and functor laws.
-- I suppose this may be useful for the demonstrarion of various foundational concepts in dependent type theory.

-- Proof of sorted list
data (<=) : (p : Nat) -> (n : Nat) -> Type where
    LeZ : 0 <= n
    LeS : p <= n -> S p <= S n

data IsSorted : List Nat -> Type where
    NilSort : IsSorted []
    SinglSort : IsSorted [x]
    ConsSort : IsSorted (y :: ys) -> x <= y -> IsSorted (x :: y :: ys)

is_sorted_0123 : IsSorted [0, 1, 2, 3]
is_sorted_0123 = ConsSort (ConsSort (ConsSort SinglSort (LeS (LeS LeZ))) (LeS LeZ)) (LeZ)


-- For sorted Successor list
is_sorted_succ : (xs : List Nat) -> IsSorted xs -> IsSorted (map S xs)
is_sorted_succ [] NilSort = NilSort
is_sorted_succ [x] SinglSort = SinglSort
is_sorted_succ (x :: (y :: ys)) (ConsSort xa ya) = ConsSort (is_sorted_succ (y :: ys) xa) (LeS ya)


-- Proofs for reflexivity and constant list sortedness
leRefl : (n : Nat) -> n <= n
leRefl 0 = LeZ
leRefl (S k) = LeS (leRefl k)

is_sorted_cst : (lg, val : Nat) -> IsSorted (replicate lg val)
is_sorted_cst Z n = NilSort
is_sorted_cst (S Z) n = SinglSort
is_sorted_cst (S (S k)) n = ConsSort (is_sorted_cst (S k) n) (leRefl n)


-- Logical connectives and implications proofs
data And : (p : Type) -> (q : Type) -> Type where
  Both : (prf_of_p : p)
      -> (prf_of_q : q)
      -> And p q

data Or : (a : Type) -> (b : Type) -> Type where
  ProofLeft  : (prf : a) -> Or a b
  ProofRight : (prf : b) -> Or a b

Implies  :  (a : Type) -> (b : Type) -> Type
Implies a b  =  a -> b


and_not_or : (a `And` b) `Implies` Not (Not a `Or` Not b)
and_not_or (Both prf_of_p prf_of_q) (ProofLeft prf) = prf prf_of_p
and_not_or (Both prf_of_p prf_of_q) (ProofRight prf) = prf prf_of_q

or_not_and : (a `Or` b) `Implies` Not (Not a `And` Not b)
or_not_and (ProofLeft prf) (Both prf_of_p prf_of_q) = prf_of_p prf
or_not_and (ProofRight prf) (Both prf_of_p prf_of_q) = prf_of_q prf

not_or : Not (a `Or` b) `Implies` (Not a `And` Not b)
not_or f = Both (\a => f (ProofLeft a)) (\b => f (ProofRight b))

not_or' : (Not a `And` Not b) `Implies` Not (a `Or` b)
not_or' (Both prf_of_p prf_of_q) (ProofLeft prf) = prf_of_p prf
not_or' (Both prf_of_p prf_of_q) (ProofRight prf) = prf_of_q prf


-- Quantifiers and logical relations
Forall : ( t : Type ) -> ( p : t -> Type ) -> Type
Forall t p = ( x : t ) -> p x

forall_or : (Forall t p `Or` Forall t q) `Implies` Forall t (\x => p x `Or` q x)
forall_or (ProofLeft prf) x = ProofLeft (prf x)
forall_or (ProofRight prf) x = ProofRight (prf x)

Exists : ( t : Type ) -> ( p : t -> Type ) -> Type
Exists = DPair

exist_p_not_p : ((Exists a p) `And` (Exists a (Not . p))) -> Not (Forall a p `Or` Forall a (Not . p))
exist_p_not_p (Both ((x ** y)) ((fst ** snd))) (ProofLeft prf) = snd (prf fst)
exist_p_not_p (Both ((x ** y)) ((fst ** snd))) (ProofRight prf) = prf x y


-- Proofs of LEM to DNE and double negation
lem_to_dne : a `Or` Not a -> Not (Not a) `Implies` a
lem_to_dne (ProofLeft prf) f = prf
lem_to_dne (ProofRight prf) f =  absurd (f prf)

not_not_lem : Not (Not (a `Or` Not a))
not_not_lem f = f (ProofRight (\x => f (ProofLeft x)))


-- Vector properties
same_length : {xs : Vect m a} -> {ys : Vect n a} -> xs = ys -> length xs = length ys
same_length Refl = Refl

same_elments : {xs , ys : Vect n a} -> xs = ys -> index i xs = index i ys
same_elments Refl = Refl

different_heads : {xs , ys : Vect n a} -> Not (x = y) -> Not (x :: xs = y :: ys)
different_heads f Refl = f Refl


-- Proofs for functor laws (unfinished)
interface Functor t => FunctorV (t : Type -> Type) where
  pres_idty : (xs : t a) -> map Prelude.id xs = xs
  pres_comp : (f : a -> b) -> (g : b -> c) -> (xs : t a) ->
    map (g . f) xs = (map g . map f) xs

FunctorV List where
  pres_idty [] = Refl
  pres_idty (x :: xs) = ?dddd
  pres_comp f g [] = Refl
  pres_comp f g (x :: xs) = ?ssss





