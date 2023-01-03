-- Computational Tree Logic (CTL)
import qualified Data.Set as Set

data Prop = Bottom
          | Atom Char
          | And Prop Prop
          | Or Prop Prop
          | Not Prop
          | ExistsNext Prop
          | ForAllNext Prop
          | ExistsUntil Prop Prop
          | ForAllUntil Prop Prop


newtype State = State Char
              deriving (Eq, Ord, Show)
type Model = (Set.Set State, [(State, State)], Set.Set State, State -> [Char])

states :: Model -> Set.Set State
states (s, _, _, _) = s

transition :: Model -> [(State, State)]
transition (_, r, _, _) = r

initStates :: Model -> Set.Set State
initStates (_, _, i, _) = i

tag :: Model -> (State -> [Char])
tag (_, _, _, l) = l

eval :: Model -> State -> Prop -> Bool
eval m s p = Set.member s (sat m p)

-- sat evaluates to the set of all states such that p holds in those states
-- Two extra cases to the pattern match were added, a) and b). These cases
-- can be treated as normal via the remaining cases, but for efficiency reasons
-- these use their own algorithm to determine the satisfying states.
sat :: Model -> Prop -> Set.Set State
sat _ Bottom = Set.empty
sat m (Atom p) = Set.fromList [s | s <- Set.toList (states m), elem p ((tag m) s)]
sat m (And p q) = Set.intersection (sat m p) (sat m q)
sat m (Or p q) = Set.union (sat m p) (sat m q)
sat m (Not p) = (states m) Set.\\ (sat m p)
sat m (ExistsNext p) = preExists (sat m p) m
sat m (ForAllNext p) = preForAll (sat m p) m
sat m (ForAllUntil (Not Bottom) p) = inevSat (sat m p) m -- a)
sat m (ExistsUntil (Not Bottom) p) = possSat (sat m p) m -- b)
sat m (ExistsUntil p q) = exUntilSat (sat m p) (sat m q) m
sat m (ForAllUntil p q) = fallUntilSat (sat m p) (sat m q) m


validOnModel :: Model -> Prop -> Bool
validOnModel m p = Set.null (Set.filter (\s -> Set.notMember s sats) (initStates m))
                  where sats = sat m p

-- Algorithms for propositions satisfaction
preExists :: Set.Set State -> Model -> Set.Set State
preExists xs m =
        Set.fromList [s | s <- ss, not (Set.disjoint (nextStates m s) xs)]
        where
          ss = Set.toList (states m)

preForAll :: Set.Set State -> Model -> Set.Set State
preForAll xs m =
        Set.fromList [s | s <- ss, Set.isSubsetOf (nextStates m s) xs]
        where
          ss = Set.toList (states m)

fallUntilSat :: Set.Set State -> Set.Set State -> Model -> Set.Set State
fallUntilSat xs ys m  | ys == y' = ys
                      | otherwise = fallUntilSat xs y' m
                  where y' = Set.union ys (Set.intersection xs (preForAll ys m))

exUntilSat :: Set.Set State -> Set.Set State -> Model -> Set.Set State
exUntilSat xs ys m  | ys == y' = ys
                    | otherwise = exUntilSat xs y' m
                  where y' = Set.union ys (Set.intersection xs (preExists ys m))

inevSat :: Set.Set State -> Model -> Set.Set State
inevSat xs m  | xs == x' = xs
              | otherwise = inevSat x' m
              where x' = Set.union xs (preForAll xs m)

possSat :: Set.Set State -> Model -> Set.Set State
possSat xs m  | xs == x' = xs
              | otherwise = possSat x' m
              where x' = Set.union xs (preExists xs m)

-- Syntactic equivalences
-- Conn represents binary logic operators (connectives)
type Conn = Prop -> Prop -> Prop
-- TrConn represents trace connectives (quantifiers over traces)
type TrConn = Prop -> Prop

imply :: Conn
imply p q = Or (Not p) q

iff :: Conn
iff p q = And (imply p q) (imply q p)

xor :: Conn
xor p q = iff p (Not q)

nor :: Conn
nor p q = Not (Or p q)

nand :: Conn
nand p q = Not (And p q)

top :: Prop
top = Not Bottom

inev :: TrConn -- Inevitable (for every path, at some point p is satisfied)
inev p = ForAllUntil top p

poss :: TrConn -- Possible (exists a state reachable where p holds)
poss p = ExistsUntil top p

inv :: TrConn -- Invariant (holds on every state reachable from the start)
inv p = Not (poss (Not p))

invT :: TrConn -- Invariant on trace (holds on every state on some trace)
invT p = Not (inev (Not p))

eP :: Prop -> Prop -> Prop
eP p q = poss (And p (ExistsNext (poss q))) -- Exists trace such that p holds before q holds

faP :: Prop -> Prop -> Prop
faP p q = inev (And p (ForAllNext (poss q))) -- In all traces p holds and eventually q holds

eR :: Prop -> Prop -> Prop
eR p q = eP p (eP q p) -- Exists trace where p holds, then q and then p again (the may not hold immediately)

faR :: Prop -> Prop -> Prop
faR p q = faP p (faP q p) -- In all traces p holds, then q and then p again (the may not hold immediately one after each other)

eHENO :: Prop -> Prop -- Exists path such that p holds on the even states of the path and doesnt hold on the odd ones
eHENO p = And p (invT (And (imply p (ExistsNext (Not p))) (imply (Not p) (ExistsNext p))))

faHENO :: Prop -> Prop -- In all paths p holds on the even states of the path and doesnt hold on the odd ones
faHENO p = And p (inv (And (imply p (ForAllNext (Not p))) (imply (Not p) (ForAllNext p))))

eRN :: Prop -> Prop -- p holds right now and doesnt on some trace again
eRN p = And p (ExistsNext (invT (Not p)))

faRN :: Prop -> Prop -- p holds right now and doesnt hold on any reachable state
faRN p = And p (ForAllNext (inv (Not p)))

-- Utilities
find :: Eq a => a -> [(a,b)] -> b
find k = snd . head . filter (\(k', _) -> k' == k)

nextStates :: Model -> State -> Set.Set State
nextStates m s = Set.fromList [s' | (s0,s') <- transition m, s0 == s]

{- Test Model
m :: Model
m = (Set.fromList [State 'a', State 'b'], [(State 'a', State 'b'), (State 'b', State 'b')], Set.fromList [State 'a'], f)
  where
    f (State 'a') = ['p']
    f (State 'b') = ['q']
-}
