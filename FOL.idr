module FOL
import Data.Vect

data Function: Type where
  F: String -> Nat -> Function

data Relation: Type where
  R: String -> Nat -> Relation

interface Opr a where
  getDeg: a -> Nat
  getName: a -> String

Opr Function where
  getDeg (F _ k) = k
  getName (F s _) = s

Opr Relation where
  getDeg (R _ k) = k
  getName (R s _) = s

infixr 10 @.
data Term: Type where
  Vari: String -> Term
  Cons: String -> Term
  (@.): (f: Function) -> Vect (getDeg f) Term -> Term

data Variable: Term -> Type where
  Free: (s:String) -> Variable (Vari s)

infixr 10 .=
infixr 10 ~>
infixr 10 \/
infixr 10 /\
infixr 10 .=>
infixr 10 .~

data Formula: Type where
  (.=): Term -> Term -> Formula
  (~>): (g: Relation) -> Vect (getDeg g) Term -> Formula
  (\/): Formula -> Formula -> Formula
  (/\): Formula -> Formula -> Formula
  (.=>): Formula -> Formula -> Formula
  (.~): Formula -> Formula -> Formula
  Not: Formula -> Formula
  ForAll: {s: String} -> (Variable (Vari s)) -> Formula -> Formula
  Exists: {s: String} -> (Variable (Vari s)) -> Formula -> Formula

toTerm: {T: Term} -> (Variable T) -> Term
toTerm (Free s) = Vari s



----------------------------------------------------------------------
---->   Language of Sets
----------------------------------------------------------------------

phi: Term
phi = Cons "emptySet"

belongs: Relation
belongs = R "belongs" 2

terms: (numVar:Nat) -> Vect (S numVar) Term
terms Z = phi :: Nil
terms (S k) = Vari ("X" ++ cast k) :: (terms k)

baseFormulas: Vect n Term -> List Formula
baseFormulas xs = crossFor xs xs where
  crossFor: Vect m Term -> Vect n Term -> List Formula
  crossFor Nil ys = Nil
  crossFor (a::xs) ys = (cross a ys) ++ (crossFor xs ys) where
    cross: Term -> Vect n Term -> List Formula
    cross _ Nil = Nil
    cross a (t::xs) = [(a .= t), (belongs ~> [a,t])] ++ (cross a xs)

setFormulas : Nat -> Nat -> List Formula
setFormulas Z numFreeVar = baseFormulas (terms numFreeVar)
setFormulas (S k) numFreeVar = (baseFormulas (terms numFreeVar)) ++
                      (recFormulas (S k) (setFormulas k numFreeVar)) ++
                      (quantFormulas (S k) numFreeVar (setFormulas k (S numFreeVar))) where
  recFormulas: Nat -> List Formula -> List Formula
  recFormulas depth xs = crossFor xs xs where
    crossFor: List Formula -> List Formula -> List Formula
    crossFor Nil ys = Nil
    crossFor (a::xs) ys = (cross a ys) ++ (crossFor xs ys) where
      cross: Formula -> List Formula -> List Formula
      cross _ Nil = Nil
      cross a (f::xs) = [(a \/ f), (a /\ f), (a .=> f), (a .~ f), (Not a)] ++ (cross a xs)
  quantFormulas: Nat -> Nat -> List Formula -> List Formula
  quantFormulas depth numFreeVar xs = cross (Free ("X" ++ cast numFreeVar)) xs where
    cross: Variable (Vari s) -> List Formula -> List Formula
    cross _ Nil = Nil
    cross a (f::xs) = [(ForAll a f), (Exists a f)] ++ (cross a xs)


closedFormulas: Nat -> List Formula
closedFormulas depth = setFormulas depth 0
