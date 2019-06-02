import Data.Maybe (fromMaybe)

-- Tipo de dato para representar expresiones de la lógica proposicional
data Prop = TTrue
           | FFalse 
           | Var String
           | Neg Prop
           | Conj Prop Prop
           | Disy Prop Prop
           | Impl Prop Prop
           | Syss Prop Prop
           deriving (Eq,Ord)

instance Show Prop where 
  show TTrue = "True" -- T
  show FFalse = "False" -- F
  show (Var x) = x -- P  
  show (Neg p) = "¬" ++ show p -- ¬ P
  show (Conj p q) = "(" ++ show p ++ " ∧ " ++ show q ++ ")" -- (P ∧ Q)
  show (Disy p q) = "(" ++ show p ++ " ∨ " ++ show q ++ ")" -- (P ∨ Q)
  show (Impl p q) = "(" ++ show p ++ " → " ++ show q ++ ")" -- (P → Q)
  show (Syss p q) = "(" ++ show p ++ " ↔ " ++ show q ++ ")" -- (P ↔ Q)

{-
    Función sacaVar, función que obtiene el nombre de cada una de las variables involucradas con la propocicion.
-}  

sacaVar :: Prop -> [String]
sacaVar TTrue = []
sacaVar FFalse = []
sacaVar (Var p) = [p]
sacaVar (Neg p) = sacaVar p
sacaVar (Conj p q) = sacaVar p ++ sacaVar q
sacaVar (Disy p q) = sacaVar p ++ sacaVar q
sacaVar (Impl p q) = sacaVar p ++ sacaVar q
sacaVar (Syss p q) = sacaVar p ++ sacaVar q


{-
    Función sinRepeticiones, función que elimina las variables repetidas
-}

sinRepeticiones :: Prop -> [String]
sinRepeticiones = quitaRepetido.sacaVar

quitaRepetido:: (Eq a) => [a] -> [a]
quitaRepetido [] = []
quitaRepetido (x:xs) = x : quitaRepetido (filter (/= x) xs)

{-
- Funcion que crea la combinacion de numeros en la tabla de verdad,
- es decir, pone los 1 y 0 correspondientes.
-}
combinacion :: [String] -> [[Int]]
combinacion [] = [[]]
combinacion (x:xs) = [b:r | b <- [0,1],r <- combinacion xs]

{-
- Funcion que asocia y regresa una lista de tuplas 
-}
asociar :: [String] -> [Int] -> [(String,Int)] -> [(String,Int)]
asociar [] _ r = r
asociar (v:vars) (b:bt) r = asociar vars bt ((v,b):r)

{-
- Funcion que resuelve una tabla de verdad dada una Prop y nos devuelve una lista de 1 y 0
-}
tablaDeVerdad :: Prop -> [Int]
tablaDeVerdad e = reverse (tablaDeVerdadAux e b [])
    where
        b = combinacion (sacaVar e)
        tablaDeVerdadAux :: Prop -> [[Int]] -> [Int] -> [Int]
        tablaDeVerdadAux _ [] r = r
        tablaDeVerdadAux e (b:bs) r = tablaDeVerdadAux e bs ((tV e b) ++ r)
          where
              tV :: Prop -> [Int] -> [Int]
              tV e b = [interpretacion e aux]
                where
                    aux = asociar (sinRepeticiones e) b []

{-
- Dada una Prop y una tupla nos regresa la interpretacion de esa prop
-}
interpretacion :: Prop -> [(String,Int)]-> Int
interpretacion (Var v) vs = fromMaybe 0 (lookup v vs)
interpretacion TTrue vs = 1
interpretacion FFalse vs = 0
interpretacion (Neg p) vs = ((interpretacion p vs)+1) `mod`2
interpretacion (Conj p q) vs = (interpretacion p vs) * (interpretacion q vs)
interpretacion (Disy p q) vs = ((interpretacion p vs) * (interpretacion q vs) + (interpretacion p vs) + (interpretacion q vs))`mod`2
interpretacion (Impl p q) vs = interpretacion (Disy (Neg p) (q)) vs
interpretacion (Syss p q) vs
    |(interpretacion p vs) == (interpretacion q vs) = 1
    |otherwise = 0


{-
    Función convierte, esta función recibe dos propociciones y 
    las regresa en forma de implicación.
-}
convierteAimpl :: Prop -> Prop -> Prop
convierteAimpl p q = Impl p q

{-
    Función correcto, esta función nos dice si bajo un conjunto de propociciones la conclusión es correcta.
    Convierte el conjunto de propociciones en conjunción de propociciones, las cuales implicaran la conclusión.
    Recibe una lista de proposiciones (conjunto de propociciones), y una proposición la cual es 
    la conclusión
-}

correcto :: [Prop] -> Prop -> Bool
correcto [] (TTrue) = True
correcto [] (FFalse) = False
correcto [] (Var x) = True
correcto [] (Impl a b) = correcto [a] b
correcto [] (Conj a b) = correcto [] a && correcto [] b
correcto [] (Disy a b) = correcto [a] b && correcto [b] a
correcto [] (Syss a b) = correcto [] (Impl a b) && correcto [] (Impl b a)
correcto (x:xs) c = verdadero (tablaDeVerdad (convierteAimpl (convierteAconj (x:xs)) c))

{-
    Función verdadero, nos dice si todos los elementos de la lista son 1. 
-}

verdadero :: [Int] -> Bool
verdadero [1] = True
verdadero [0] = False
verdadero (x:xs) = if x == 1 then True && verdadero xs else False


{-
    Función convierteAconj, regresa la conjunción de cada una de 
    las propociciones dentro del conjunto de propociciones.
 -Hay pdos
-}
convierteAconj :: [Prop] -> Prop
convierteAconj (x:xs) = if xs /= [] then Conj x (convierteAconj xs) else x

p = correcto [(Syss (Var "P") (Var "Q")), (Var "P")] (Var "Q")
q = correcto [(Impl (Var "P") (Var "Q")), (Var "P")] (Var "Q")

tb = tablaDeVerdad (Impl (Conj (Impl (Var "P") (Var "Q")) (Var "P")) (Var "Q"))