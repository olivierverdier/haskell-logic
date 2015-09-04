{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleContexts #-}

import Control.Applicative ((<*>))



type a :+: b = Either a b
type a :&: b = (a,b)


data a :<->: b = (a -> b) :&: (b -> a)

{- Commutativity, associativity and distributivity of "or" and "and" -}
andCommut :: a :&: b -> b :&: a
andCommut (x,y) = (y,x)

orCommut :: a :+: b -> b :+: a
orCommut (Left x) = Right x
orCommut (Right y) = Left y

andAssoc :: ((a :&: b) :&: c) -> (a :&: (b :&: c))
andAssoc ((x,y),z) = (x,(y,z))

orAssoc :: ((a :+: b) :+: c) -> (a :+: (b :+: c))
orAssoc (Left (Left x)) = Left x
orAssoc (Right z) = Right $ Right z
orAssoc (Left (Right y)) = Right $ Left y

andDist :: a :&: (b :+: c) -> (a :&: b) :+: (a :&: c)
andDist (x, Left y) = Left (x,y)
andDist (x, Right z) = Right (x,z)

andCoDist :: (a :&: b) :+: (a :&: c) -> a :&: (b :+: c)
andCoDist (Left (x,y)) = (x, Left y)
andCoDist (Right (x,z)) = (x, Right z)

orDist :: a :+: (b :&: c) -> (a :+: b) :&: (a :+: c)
orDist (Left x) = (Left x, Left x)
orDist (Right (y,z)) = (Right y, Right z)

orCoDist :: (a :+: b) :&: (a :+: c) -> a :+: (b :&: c)
orCoDist (Left x, _) = Left x -- not canonical?
orCoDist (_, Left x) = Left x
orCoDist (Right y, Right z) = Right (y,z)




modusPonens :: (a -> b) :&: a -> b
modusPonens = uncurry ($)

reflexivity :: a -> a
reflexivity = id

commutativity :: (a -> b -> c) -> b -> a -> c
commutativity = flip

andIntro :: a -> b -> a :&: b
andIntro = (,)


const' :: b -> a -> b
const' = const

-- orProj :: a :+: a -> a
-- orProj (Left x) = x
-- orProj (Right x) = x

sCombi :: (a -> b -> c) -> (a -> b) -> a -> c -- also called distributivity
-- sCombi f g x = f x $ g x
sCombi = (<*>)

simplification1 :: a :&: b -> a
simplification1 = fst

simplification2 :: a :&: b -> b
simplification2 = snd

introduction1 :: a -> a :+: b
introduction1 = Left

introduction2 :: b -> a :+: b
introduction2 = Right

disjelim :: (a -> d) -> (b -> d) -> a :+: b -> d
disjelim f _ (Left x) = f x
disjelim _ g (Right y) = g y

consDilemma :: (a -> b) -> (a' -> b') -> a :&: a' -> b :&: b'
consDilemma f g (x, y) = (f x, g y)

absorption :: (a -> b) -> a -> a :&: b
absorption f x = (x, f x)

exportation :: (a :&: b -> d) -> a -> b -> d
exportation = curry

{- Pseudo negation -}

type Not c a = a -> c

contradiction :: Not c (a :&: Not c a)
contradiction = uncurry $ flip ($)

destDilemma :: (a -> b) -> (a' -> b') -> Not c b :+: Not c b' -> Not c a :+: Not c a'
destDilemma f _ (Left x) = Left $ pb f x
destDilemma _ f' (Right x') = Right $ pb f' x'


modusPonendoTollens :: Not c (a :&: b) -> a -> Not c b
modusPonendoTollens f x y = f (x,y)

negationIntro :: (a -> b) -> (a -> Not c b) -> Not c a
negationIntro f f' x = contradiction (f x, f' x)


{- Pull back, or modus tollens, or contramap in Haskell -}
pb :: (a -> b) -> Not c b -> Not c a
pb = flip (.)



{- Potential statements -}
type Pot c a = Not c (Not c a)

-- return in the continuation monad
dn :: a -> Pot c a -- Double negation
dn = flip ($)

-- functor property
pfmap :: (a -> b) -> Pot c a -> Pot c b
pfmap = pb . pb

-- pbind :: (a -> Pot c b) -> Pot c a -> Pot c b

-- pap :: Pot c (a -> b) -> Pot c a -> Pot c b
-- pap f = pfmap f . dn

potNot :: Pot c (Not c a) -> Not c a
potNot = pb dn

potPot :: Pot c (Pot c a) -> Pot c a
potPot = potNot


contraposition' :: (Not c b -> Not c a) -> a -> Pot c b
contraposition' g a = pb g $ dn a

{- anti Distributivity of Not -}

andNot :: Not c a :&: Not c b -> Not c (a :+: b)
andNot (nx, ny) = g where
	g (Left x) = nx x
	g (Right y) = ny y
-- andNot = pb or_NotNot . dn

notOr :: Not c (a :+: b) -> Not c a :&: Not c b
notOr n = (n . Left, n . Right)

orNot :: Not c a :+: Not c b -> Not c (a :&: b)
orNot (Left nx) = nx . fst
orNot (Right ny) = ny . snd


notAnd'' :: Not c (Pot c a :&: Pot c b) -> Pot c (Not c a :+: Not c b)
notAnd'' = pb notOr



{- -}

and_NotNot :: a :&: b -> Not c (Not c a :+: Not c b)
and_NotNot (x,_) (Left nx) = nx x
and_NotNot (_,y) (Right ny) = ny y

and_andPot :: a :&: b -> (Pot c a :&: Pot c b)
and_andPot = notOr . and_NotNot

or_NotNot :: a :+: b -> Not c (Not c a :&: Not c b)
or_NotNot (Left x) (nx,_) = nx x
or_NotNot (Right y) (_,ny) = ny y

-- potOr :: Pot c (a :+: b) -> Not c (Not c a :&: Not c b)

{- Inference -}

{- Conjunctive inference -}

inf1 :: a :&: b -> Not c (a -> Not c b)
inf1 (x,y) f = f x y

inf1_ :: (a -> Not c b) -> Not c (a :&: b)
inf1_ = flip inf1

inf1__ ::  Not c (a :&: b) -> (a -> Not c b)
inf1__ f x y = f (x,y)

inf2 :: (a -> b) -> Not c (a :&: Not c b)
inf2 f (x, ny) = ny $ f x

-- inf3
inference' :: a :&: Not c b -> Not c (a -> b)
inference' (x, ny) g = ny . g $ x


inference'' :: (Pot c a -> b) -> Pot c (Not c a :+: Pot c b)
inference'' = notAnd'' . pb inference' . dn . (dn .)

{- Absurdity -}

class Absurd c a where
	absurd :: c -> a

{- Disjunctive inference -}
-- disImp1 :: (Absurd c b) => a :+: b -> Not c a -> b
-- disImp1 (Left x) nx = absurd $ nx x
-- disImp1 (Right y) _ = y

disjunctive :: Absurd c b => (a :+: b) -> Not c a -> b
disjunctive (Left x) nx = absurd . nx $ x
disjunctive (Right y) _ = y

coinference :: (Absurd c b) => Not c a :+: b -> a -> b
coinference (Left nx) = absurd . nx
coinference (Right y) = const y


{- Peirce's law -}

orfmap :: (a -> b) -> (a :+: c) -> (b :+: c)
orfmap f = orCommut . fmap f . orCommut

andOr :: (a :&: b) :+: a -> a
andOr (Left (x,_)) = x
andOr (Right x) = x

prePeirce' :: (Pot c (Not c a :+: b) -> a) -> Pot c a
prePeirce' = potPot . pfmap andOr . (pfmap . orfmap) notOr . inference''

peirce' :: Absurd c b => (Pot c (a -> b) -> a) -> Pot c a
peirce' = prePeirce' . (pb . pfmap $ coinference)

{- Reductio ad absurdum -}

type ReductioT c a = Pot c a -> a

class Reductio c a where
	lem :: ReductioT c a


contraposition :: (Reductio c b) => (Not c b -> Not c a) -> a -> b
contraposition g a = lem $ pb g $ dn a

lift :: (Reductio c a) => (a -> b) -> Pot c a -> b
lift = (. lem)

inference :: (Reductio c a, Reductio c (Not c a :+: Pot c b)) => (a -> b) -> Not c a :+: Pot c b
inference = lem . notAnd'' . pb inference' . dn . (dn .) . (. lem)

doubleLem :: (Reductio c a, Reductio c b) => Pot c a :&: Pot c b -> a :&: b
doubleLem (x,y) = (lem x, lem y)

notAnd :: (Reductio c a, Reductio c b, Reductio c (Not c a :+: Not c b)) => Not c (a :&: b) -> Not c a :+: Not c b
notAnd = lem . pb notOr . pb doubleLem

notAnd_ :: ReductioT c a -> ReductioT c b -> ReductioT c (Not c a :+: Not c b) -> Not c (a :&: b) -> Not c a :+: Not c b
notAnd_ lema lemb lemaob = lemaob . pb notOr . pb ( \ (x,y) -> (lema x, lemb y) )

peirce1 :: (Reductio c (a -> b), Absurd c b) => ((a -> b) -> a) -> Pot c a
peirce1 = peirce' . lift

peirce2 :: (Reductio c a, Absurd c b) => (Pot c (a -> b) -> a) -> a
peirce2 = lem . peirce'

-- peirce :: (Reductio c a, Reductio c (a -> b), Absurd c b) => ((a -> b) -> a) -> a
-- peirce lem = lem . peirce' . lift

fromLem :: (Absurd c a) => a :+: Not c a -> Pot c a -> a
fromLem (Left x) _ = x
fromLem (Right nx) px = absurd $ px nx

toLem' :: (Pot c a -> a) 
	-> (Not c a -> Not c a)
toLem' lm = potNot . pb lm

toLem :: (Pot c a -> a)
	-> Not c (Not c a :&: a)
toLem = inf1_ . toLem'

lemma' :: ReductioT c a -> ReductioT c (Pot c a :+: Not c a) -> Not c (Not c a :&: a) -> Pot c a :+: Not c a
lemma' lema lemnaa = notAnd_ potNot lema lemnaa
