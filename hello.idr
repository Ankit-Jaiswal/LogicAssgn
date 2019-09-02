module Hello

x: Nat
x = 42

foo: String
foo = "Sausage machine"

bar: Char
bar = 'Z'

quux: Bool
quux = False


infixr 10 :::
data Lost a = Nil | (:::) a (Lost a)

isEven : Nat -> Bool
isEven Z = True
isEven (S k) = isOdd k where
    isOdd Z = False
    isOdd (S k) = isEven k


infixr 10 +:
data Vect: Nat -> Type -> Type where
    Emp : Vect Z a
    (+:) : a -> Vect k a -> Vect (S k) a

isEmpty: Vect n a -> Bool
isEmpty {n = Z} _ = True
isEmpty {n = S k} _ = False

data Natural: Type where
  Zero: Natural
  Succ: Natural -> Natural


third: Nat -> Nat
third n = (first n) + (second n) where
  first : Nat -> Nat
  first n = n
  second: Nat -> Nat
  second n = n
