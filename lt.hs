-- Logica Temporal - Computer Tree Logic (CTL)


data Prop = Bottom
          | Atom Char
          | Or Prop Prop
          | Not Prop
          | ExN Prop -- Exists Next
          | FAllN Prop -- For All Next
          | ExU Prop Prop -- Exists Until
          | FAllU Prop Prop -- For All Until


newtype State = Char
data Model = ([State], [(State, State)], [State], State -> [Char])

states :: Model -> [State]
states (S, _, _, _) = S

transition :: Model -> [(State, State)]
transition (_, R, _, _) = f

initStates :: Model -> [State]
initStates (_, _, I, _) = I

tag :: Model -> (State -> [Char])
tag (_, _, _, L) = L


eval :: Model -> State -> Prop -> Bool
eval _ _ Bottom = False
eval M

sat :: Model -> Prop -> Bool


-- Algoritmos de satisfaccion de proposiciones
--preExists :: [State] -> Model -> [State]
-- preExists xs = [s | s <- (states M), ]

--preForAll :: [State] -> [State]


-- exUntil ::
-- inev ::

-- Utilidades
inList :: Eq a => a -> [a] -> Bool
inList x = or . (map (\x' -> x' == x))

find :: Eq a => a -> [(a,b)] -> b
find k = snd . head . filter (\(k', _) -> k' == k)
