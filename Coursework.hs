
--------------------------------------------
--                                        --
-- CM20256/CM50262 Functional Programming --
--                                        --
--         Coursework 2020/2021           --
--                                        --
--------------------------------------------


------------------------- Auxiliary functions

find :: (Show a,Eq a) => a -> [(a,b)] -> b
find x [] = error ("find: " ++ show x ++ " not found")
find x ((y,z):zs)
  | x == y    = z
  | otherwise = find x zs


merge :: Ord a => [a] -> [a] -> [a]
merge xs [] = xs
merge [] ys = ys
merge (x:xs) (y:ys)
    | x == y    = x : merge xs ys
    | x <= y    = x : merge xs (y:ys)
    | otherwise = y : merge (x:xs) ys

minus :: Ord a => [a] -> [a] -> [a]
minus xs [] = xs
minus [] ys = []
minus (x:xs) (y:ys)
    | x <  y    = x : minus    xs (y:ys)
    | x == y    =     minus    xs    ys
    | otherwise =     minus (x:xs)   ys


------------------------- Lambda-terms

type Var = String

data Term =
    Variable Var
  | Lambda   Var  Term
  | Apply    Term Term
  deriving Eq


instance Show Term where
  show = f 0
    where
      f i (Variable x) = x
      f i (Lambda x m) = if i /= 0 then "(" ++ s ++ ")" else s where s = "\\" ++ x ++ ". " ++ f 0 m 
      f i (Apply  n m) = if i == 2 then "(" ++ s ++ ")" else s where s = f 1 n ++ " " ++ f 2 m

free :: Term -> [Var]
free (Variable x) = [x]
free (Lambda x n) = free n `minus` [x]
free (Apply  n m) = free n `merge` free m


------------------------- Types

infixr 5 :->

type Atom = String
data Type = At Atom | Type :-> Type
  deriving Eq

instance Show Type where
  show (At a)       = a
  show (At a :-> s) = a ++ " -> " ++ show s
  show    (t :-> s) = "(" ++ show t ++ ") -> " ++ show s


atoms :: [Atom]
atoms = map (:[]) ['a'..'z'] ++ [ a : show i | i <- [1..], a <- ['a'..'z'] ]

t1 :: Type
t1 = At "a" :-> At "b"

t2 :: Type
t2 = (At "c" :-> At "d") :-> At "e"

t3 :: Type
t3 = At "a" :-> At "c" :-> At "c"

------------------------- Assignment 1

occurs :: Atom -> Type -> Bool
occurs x (At y) = x == y
occurs x (s :-> t) = occurs x s || occurs x t

findAtoms :: Type -> [Atom]
findAtoms (At x) = [x] 
findAtoms (At x :-> s) = merge [x] (findAtoms s)
findAtoms (s :-> t) = merge (findAtoms s) (findAtoms t)


------------------------- Type substitution

type Sub = (Atom,Type)

s1 :: Sub
s1 = ("a", At "e")

s2 :: Sub
s2 = ("e", At "b" :-> At "c")

s3 :: Sub
s3 = ("c", At "a" :-> At "a")


------------------------- Assignment 2

sub :: Sub -> Type -> Type
sub (x, y) (At z)
  | x == z = y
  | otherwise = At z
sub x (y :-> z) = sub x y :-> sub x z


subs :: [Sub] -> Type -> Type
subs [x] y = sub x y
subs (x:xs) y = sub x (subs xs y)


------------------------- Unification

type Upair = (Type,Type)
type State = ([Sub],[Upair])

u1 :: Upair
u1 = (t1,At "c")
-- u1 = (At "a" :-> At "b", At "c")
u2 :: Upair
u2 = (At "a" :-> At "a",At "a" :-> At "c")

u3 :: Upair
u3 = (t1,t2)

u4 :: Upair
u4 = (t2,t3)

st1 :: State
st1 = ([],[u1,u2])
-- st1 = ([], [(At "a" :-> At "b", At "c"), (At "a" :-> At "a",At "a" :-> At "c")])

------------------------- Assignment 3

sub_u :: Sub -> [Upair] -> [Upair]
sub_u x [] = []
sub_u x [(y, z)] = [(sub x y, sub x z)]
sub_u x ((y, z):ys) = (sub x y, sub x z) : sub_u x ys


step :: State -> State
step (x, (s,t):ys)
  | s == t = (x, ys)
step (x, (At s, t):ys)
  | occurs s t = error "Atom occurs in type"
  | otherwise = (x ++ [(s, t)], sub_u (s, t) ys) 
step (x, (s, At t):ys)
  | occurs t s = error "Atom occurs in type"
  | otherwise = (x ++ [(t, s)], sub_u (t, s) ys)
step (x, (y1 :-> y2, z1 :-> z2):ys) = (x, (y1, z1):(y2, z2):ys)

unify :: [Upair] -> [Sub]
unify x = reverse (getSubs ([], x))

getSubs :: State -> [Sub]
getSubs (x, []) = x
getSubs (x, y) = getSubs (step (x, y))

------------------------- Assignment 4

type Context   = [(Var, Type)]
type Judgement = (Context, Term, Type)

data Derivation = Axiom Judgement
                | Abstraction Judgement Derivation
                | Application Judgement Derivation Derivation


n1 = Apply (Lambda "x" (Variable "x")) (Variable "y")


n2 = Apply (Lambda "x" (Variable "x")) (Lambda "y" (Variable "y"))

d1 = Application ([("y",At "a")], n1 , At "a") (
       Abstraction ([("y",At "a")],Lambda "x" (Variable "x"),At "a" :-> At "a") (
         Axiom ([("x",At "a"),("y",At "a")],Variable "x",At "a")
     ) ) (
       Axiom ([("y",At "a")], Variable "y", At "a")
     )


d2 = Application ([("y",At "b")],Apply (Lambda "x" (Apply (Variable "x") (Variable "y"))) (Lambda "z" (Variable "z")),At "a") (
       Abstraction ([("y",At "b")],Lambda "x" (Apply (Variable "x") (Variable "y")),At "c") (
         Application ([("x",At "d"),("y",At "b")],Apply (Variable "x") (Variable "y"),At "e") (
           Axiom ([("x",At "d"),("y",At "b")],Variable "x",At "f")
         ) (
           Axiom ([("x",At "d"),("y",At "b")],Variable "y",At "g")
     ) ) ) (
       Abstraction ([("y",At "b")],Lambda "z" (Variable "z"),At "h") (
         Axiom ([("z",At "i"),("y",At "b")],Variable "z",At "j")
     ) )

conclusion :: Derivation -> Judgement
conclusion (Axiom j) = j
conclusion (Abstraction j x) = j
conclusion (Application j x y) = j

subs_ctx :: [Sub] -> Context -> Context
subs_ctx x [(y, z)] = [(y, subs x z)]
subs_ctx x ((y, z):ys) = [(y, subs x z)] ++ subs_ctx x ys

subs_jdg :: [Sub] -> Judgement -> Judgement
subs_jdg w (x, y, z) = (subs_ctx w x, y, subs w z)

subs_der :: [Sub] -> Derivation -> Derivation
subs_der w (Axiom j) = Axiom (subs_jdg w j)
subs_der w (Abstraction j x)= Abstraction (subs_jdg w j) (subs_der w x)
subs_der w (Application j x y)= Application (subs_jdg w j) (subs_der w x) (subs_der w y) 


------------------------- Typesetting derivations


instance Show Derivation where
  show d = unlines (reverse strs)
    where
      (_,_,_,strs) = showD d

      showC :: Context -> String
      showC [] = []
      showC [(x,t)]    = x ++ ": " ++ show t
      showC ((x,t):cx) = x ++ ": " ++ show t  ++ " , " ++ showC cx

      showJ :: Judgement -> String
      showJ ([],n,t) =              "|- " ++ show n ++ " : " ++ show t
      showJ (cx,n,t) = showC cx ++ " |- " ++ show n ++ " : " ++ show t

      showL :: Int -> Int -> Int -> String
      showL l m r = replicate l ' ' ++ replicate m '-' ++ replicate r ' '

      showD :: Derivation -> (Int,Int,Int,[String])
      showD (Axiom j) = (0,k,0,[s,showL 0 k 0]) where s = showJ j; k = length s
      showD (Abstraction j d)   = addrule (showJ j) (showD d)
      showD (Application j d e) = addrule (showJ j) (sidebyside (showD d) (showD e))

      addrule :: String -> (Int,Int,Int,[String]) -> (Int,Int,Int,[String])
      addrule x (l,m,r,xs)
        | k <= m     = (ll,k,rr, (replicate ll ' ' ++ x ++ replicate rr ' ') : showL  l m r  : xs)
        | k <= l+m+r = (ll,k,rr, (replicate ll ' ' ++ x ++ replicate rr ' ') : showL ll k rr : xs)
        | otherwise  = (0,k,0, x : replicate k '-' : [ replicate (-ll) ' ' ++ y ++ replicate (-rr) ' ' | y <- xs])
        where
          k = length x
          i = div (m - k) 2
          ll = l+i
          rr = r+m-k-i

      extend :: Int -> [String] -> [String]
      extend i strs = strs ++ repeat (replicate i ' ')

      sidebyside :: (Int,Int,Int,[String]) -> (Int,Int,Int,[String]) -> (Int,Int,Int,[String])
      sidebyside (l1,m1,r1,d1) (l2,m2,r2,d2)
        | length d1 > length d2 = ( l1 , m1+r1+2+l2+m2 , r2 , [ x ++ "  " ++ y | (x,y) <- zip d1 (extend (l2+m2+r2) d2)])
        | otherwise             = ( l1 , m1+r1+2+l2+m2 , r2 , [ x ++ "  " ++ y | (x,y) <- zip (extend (l1+m1+r1) d1) d2])



------------------------- Assignment 5


derive0 :: Term -> Derivation
derive0 x = aux ([], x, At "")
  where
    aux :: Judgement -> Derivation
    aux (x, Variable y, z) = Axiom (reverse c, Variable y, z)
      where c = x ++ adjustContext (free (Variable y)) x
    aux (w, Lambda x y, z) = Abstraction (reverse c, Lambda x y, z) (aux (c, y, At ""))
      where c = w ++ adjustContext (free (Lambda x y)) w
    aux (w, Apply x y, z) = Application (reverse c, Apply x y, At "") (aux (c, x, At "")) (aux (c, y, At ""))
      where c = w ++ adjustContext (free (Apply x y)) w


-- This function looks for free variables unique to the current context in question.
adjustContext :: [Var] -> Context -> Context
adjustContext [] y = []                                             -- If called with no free variables will return an empty list as no context can be created
adjustContext [x] [] = [(x, At "")]                                 -- If there is no current context the free variable becomes the context
adjustContext [x] ((y, z):ys)                                       -- If there is a free variable and a context this will check if that variable is already in the context
  | x == y = []                                                     -- If it is then an empty list is returned as the variable isn't unique
  | otherwise = adjustContext [x] ys                                -- Goes on to check if it's unique compared to the rest
adjustContext (x:xs) y = adjustContext [x] y ++ adjustContext xs y  -- Breaks list of variables into list of length 1 and goes through the above patterns

derive1 :: Term -> Derivation
derive1 = undefined
  where
    aux :: [Atom] -> Judgement -> Derivation
    aux = undefined


upairs :: Derivation -> [Upair]
upairs = undefined


derive :: Term -> Derivation
derive = undefined

