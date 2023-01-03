-- Evaluador semantico para logicas de grado 0 (Logica Proposicional)

-- Tipo de dato recursivo para definir PROP
data Prop = Bottom
          | Atom Char
          | Or Prop Prop
          | And Prop Prop
          | Imply Prop Prop
          | Not Prop
          deriving (Show, Read)

-- Valuacion para proposiciones atomicas
type Val = [(Char, Bool)]

-- Evalua una proposicion dada una valuacion
eval :: Prop -> Val -> Bool
eval Bottom _ = False
eval (Atom c) v = find c v
eval (Not p) v = not (eval p v)
eval (Or p q) v = max (eval p v) (eval q v)
eval (And p q) v = min (eval p v) (eval q v)
eval (Imply p q) v = (eval p v) <= (eval q v)

-- Evalua un conjunto de proposiciones
evalSet :: [Prop] -> Val -> [Bool]
evalSet ps v = map (\p -> eval p v) ps

-- Retorna el nombre de todas las variables atomicas que aparecen
-- la entrada
getAtoms :: Prop -> [Char]
getAtoms = elimRep . atomsProp


-- Sustitucion en proposiciones
-- sust p q c = p[q/c] donde c es el nombre de una variable atomica
sust :: Prop -> Prop -> Char -> Prop
sust Bottom _ _ = Bottom
sust (Atom c') q c  | c' == c = q
                    | otherwise = (Atom c')
sust (Not p) q c = Not (sust p q c)
sust (And p q) r c = And (sust p r c) (sust q r c)
sust (Or p q) r c = Or (sust p r c) (sust q r c)
sust (Imply p q) r c = Imply (sust p r c) (sust q r c)


-- Evalua una proposicion en todas las valuaciones significativas
-- Esto es, todas las combinaciones de valores para las proposiciones
-- atomicas que suceden en la proposicion
evalAll :: Prop -> [Bool]
evalAll p = [eval p v' | v' <- getVals (getAtoms p)]

isTautology :: Prop -> Bool
isTautology = and . evalAll

isValid :: Prop -> Bool
isValid = or . evalAll

-- Is contradiction
isCtr :: Prop -> Bool
isCtr = not . isValid

-- Equivalencias sintaticas
-- Conn representa operadores logicos binarios
type Conn = Prop -> Prop -> Prop

iff :: Conn
iff p q = And (Imply p q) (Imply q p)

xor :: Conn
xor p q = And (Imply p (Not q)) (Imply q (Not p))

nor :: Conn
nor p q = Not (Or p q)

nand :: Conn
nand p q = Not (And p q)

top :: Prop
top = Not Bottom

-- Relaciones logicas - Secuente y equivalencia
(~~) :: Prop -> Prop -> Bool
(~~) p q = isTautology (iff p q)

(|=) :: [Prop] -> Prop -> Bool
(|=) gamma p = isTautology (Imply (setToProp gamma) p)

{-
- Utilidades
-}

find :: Eq a => a -> [(a,b)] -> b
find k = snd . head . filter (\(k', _) -> k' == k)

atomsProp :: Prop -> [Char]
atomsProp Bottom = []
atomsProp (Atom c) = [c]
atomsProp (And p q) = atomsProp p ++ atomsProp q
atomsProp (Or p q) = atomsProp p ++ atomsProp q
atomsProp (Imply p q) = atomsProp p ++ atomsProp q
atomsProp (Not p) = atomsProp p

setToProp :: [Prop] -> Prop
setToProp [] = top
setToProp [p] = p
setToProp (p:ps) = And p (setToProp ps)

elimRep :: Eq a => [a] -> [a]
elimRep [] = []
elimRep (x:xs) = x : filter (/= x) (elimRep xs)

getVals :: [Char] -> [Val]
getVals [] = [[]]
getVals (c:cs) = [(c, b) : v' | b <- [True, False], v' <- getVals cs]


-- Class instances declaration

instance Eq Prop where
  (==) = (~~)

{-
instance Ord Prop where
  (<) p q = [p] |= q
  (<=) p q = ([p] < q) || (p == q)
-}
