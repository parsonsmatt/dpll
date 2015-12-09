module Prover where

import DPLL hiding ((/\))

{-
Resolution is where you get to do:

1. $A: \neg S \lor P$
2. $B: S \lor P$
3  By $A \land B$: $P$.

To 
-}

data Expr a
  = Lit a
  | Expr a :/\: Expr a
  | Expr a :\/: Expr a
  | Not (Expr a)
  deriving (Show, Eq)

instance Functor Expr where
  fmap f (Lit a) = Lit (f a)
  fmap f (a :/\: b) = fmap f a :/\: fmap f b
  fmap f (a :\/: b) = fmap f a :\/: fmap f b
  fmap f (Not a) = Not (fmap f a)

data Eval a
  = Eval
  { add :: a -> a -> a
  , mul :: a -> a -> a
  , neg :: a -> a
  }

infixr 4 :/\:
infixr 5 :\/:

evalWith :: Eval a -> Expr a -> a
evalWith _ (Lit a) = 
  a
evalWith e (a :/\: b) =
  mul e (evalWith e a) (evalWith e b)
evalWith e (a :\/: b) =
  add e (evalWith e a) (evalWith e b)
evalWith e (Not a) =
  neg e (evalWith e a)

bool :: Eval Bool
bool = Eval (||) (&&) not

eval :: Expr Bool -> Bool
eval = evalWith bool

(/\), (\/) :: Expr Bool -> Expr Bool -> Expr Bool
(/\) = (:/\:)
(\/) = (:\/:)

infixr 4 /\
infix 5 \/


true, false :: Expr Bool
true = Lit True
false = Lit False

{-
So we start with an initial list of clauses in CNF.
Then we choose something we want to prove using the knowledge base, and add
it's negation to the list of clauses.

From there, we pick a clause, pick a clause that it can resolve with, and
apply resolution to the pair. The result is added to the list of available
clauses. Eventually, no interesting clauses can be made!
-}

type KnowledgeBase a = [Expr a]

{-
Finding the fixed point of a structure and a function is easy to express as a
hylomorphism. When the type of everything is the same, we can use the `maybe`
function to build it.
-}

resolution :: (KnowledgeBase a -> Maybe (KnowledgeBase a)) -> KnowledgeBase -> KnowledgeBase
resolution f kb = maybe kb (resolution f) (f kb)

{-
Now we need to specify what we'd pass in to resolve our function. The general
structure is going to be "If the new set is the same as the old set, we've
reached the fix point. Otherwise, iterate."
We'll begin by defining resolution on two expressions.
-}

resolve :: Eq a => Expr a -> Expr a -> Maybe (Expr a)
resolve (Lit a) (Lit b) = Just $ Lit a :/\: Lit b

resolve (Lit a) (Not (Lit b))
  | a == b    = Nothing
  | otherwise = Just $ Lit a :/\: Not (Lit b)

resolve (Not (Lit a)) (Lit b) =
  Just $ resolve (Lit b) (Not (Lit a))

resolve (Lit a :\/: Lit b) (Lit c)
  | a == c    = Lit b :\/: Lit c
  | otherwise =  
