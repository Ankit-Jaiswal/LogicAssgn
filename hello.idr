module Hello

x: Nat
x = 42

foo: String
foo = "Sausage machine"

bar: Char
bar = 'Z'

quux: Bool
quux = False

isEven : Nat -> Bool
isEven Z = True
isEven (S k) = isOdd k where
    isOdd Z = False
    isOdd (S k) = isEven k