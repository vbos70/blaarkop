import Distribution.Parsec (Parsec(parsec))
import Text.XHtml (p)
import Data.Time.Format.ISO8601 (yearFormat)
import Distribution.Simple.Utils (xargs)
data ProcessGraph = 
    Deadlock
    | Empty
    | Act String
    | Proc String ProcessGraph
    | Seq ProcessGraph ProcessGraph
    | Alt ProcessGraph ProcessGraph
    | Mrg ProcessGraph ProcessGraph
    | Lmr ProcessGraph ProcessGraph
    | Cmr ProcessGraph ProcessGraph
    deriving (Show, Eq, Ord)


x = Proc "x" (Seq (Act "a") x) -- X = a ; X

eval :: ProcessGraph -> ProcessGraph
eval (Seq Empty p) = eval p
eval (Seq Deadlock p) = Deadlock
eval (Seq p1 p2) = Seq (eval p1) (eval p2) 
eval (Alt Deadlock p) = eval p
eval (Alt p Deadlock) = eval p
eval (Alt p1 p2) = Alt (eval p1) (eval p1) 
eval p = p -- otherwise


merge :: ProcessGraph -> ProcessGraph -> ProcessGraph
merge p q = Alt (cmerge p q) (Alt (lmerge p q) (lmerge q p)) 

lmerge :: ProcessGraph -> ProcessGraph -> ProcessGraph
lmerge Deadlock p = p
lmerge Empty p = p
lmerge (Act s) p = Seq (Act s) p
lmerge (Seq (Act s) p) q = Seq (Act s) (merge p q)
lmerge (Alt p q) r = Alt (lmerge p r) (lmerge q r)

cmerge :: ProcessGraph -> ProcessGraph -> ProcessGraph
cmerge (Act s) (Act t) = Act (s ++ "," ++ t)
cmerge (Seq (Act s) p) q = cmerge (Act s) q
cmerge p (Seq (Act s) q) = cmerge p (Act s)
cmerge (Alt p q) r = Alt (cmerge p r) (cmerge q r)
cmerge _ _ = Deadlock -- otherwise

act :: String -> ProcessGraph
act = Act

acts = map act

sqn [] = Empty
sqn (a: as) = Seq a (sqn as)

alt [] = Deadlock
alt (a:as) = Alt a (alt as)

-- delta ; x = x
fwdSeqDeadlockX :: ProcessGraph -> ProcessGraph
fwdSeqDeadlockX (Seq Deadlock x) = x
fwdSeqDeadlockX x = x

revSeqDeadlockX :: ProcessGraph -> ProcessGraph
revSeqDeadlockX x = Seq Deadlock x

-- empty ; x = x
fwdSeqEmptyX :: ProcessGraph -> ProcessGraph
fwdSeqEmptyX (Seq Empty x) = x
fwdSeqEmptyX x = x

revSeqEmptyX :: ProcessGraph -> ProcessGraph
revSeqEmptyX x = Seq Empty x

-- x ; empty = x
fwdSeqXEmpty :: ProcessGraph -> ProcessGraph
fwdSeqXEmpty (Seq x Empty) = x
fwdSeqXEmpty x = x

revSeqXEmpty :: ProcessGraph -> ProcessGraph
revSeqXEmpty x = Seq x Empty

-- (x ; y) ; z = x ; (y ; z)
fwdSeqSeq :: ProcessGraph -> ProcessGraph
fwdSeqSeq (Seq (Seq x y) z) = (Seq x (Seq y z)) 
fwdSeqSeq x = x

revSeqSeq :: ProcessGraph -> ProcessGraph
revSeqSeq (Seq x (Seq y z))  = (Seq (Seq x y) z)
revSeqSeq x = x

-- delta + x = x
fwdAltDeadlockX :: ProcessGraph -> ProcessGraph
fwdAltDeadlockX (Alt Deadlock x) = x
fwdAltDeadlockX x = x

revAltDeadlockX :: ProcessGraph -> ProcessGraph
revAltDeadlockX x = (Alt Deadlock x)

-- x + delta = x
fwdAltXDeadlock :: ProcessGraph -> ProcessGraph
fwdAltXDeadlock (Alt x Deadlock) = x
fwdAlXDeadlock x = x

revAltXDeadlock :: ProcessGraph -> ProcessGraph
revAltXDeadlock x = (Alt x Deadlock)

-- (x + y) + z = x + (y + z)
fwdAltAlt :: ProcessGraph -> ProcessGraph
fwdAltAlt (Alt (Alt x y) z) = (Alt x (Alt y z)) 
fwdAltAlt x = x

revAltAlt :: ProcessGraph -> ProcessGraph
revAltAlt (Alt x (Alt y z))  = (Alt (Alt x y) z)
revAltAlt x = x

-- (x + y) ; z = (x ; z) + (y ; z)
fwdSeqAltXYZ :: ProcessGraph -> ProcessGraph
fwdSeqAltXYZ (Seq (Alt x y) z) = Alt (Seq x z) (Seq y z)
fwdSeqAltXYZ x = x

revSeqAltXYZ :: ProcessGraph -> ProcessGraph
revSeqAltXYZ (Alt (Seq x z1) (Seq y z2))
    | z1 == z2 = Seq (Alt x y) z1
    | otherwise = Alt (Seq x z1) (Seq y z2)
revSeqAltXYZ x = x

step :: ProcessGraph -> ProcessGraph -> Bool
step x y
    | x == y = True
    | otherwise = False

calc:: [ProcessGraph] -> Bool
calc [] = True
calc [x] = True
calc (x : y : xs)
    | step x y = calc (y : xs)
    | otherwise = False


c1 = [
    Alt (Seq Deadlock (Seq Deadlock Empty)) Empty,
    Alt (Seq Deadlock (fwdSeqDeadlockX (Seq Deadlock Empty))) Empty,
    Alt (Seq Deadlock Deadlock) Empty,
    Alt (fwdSeqDeadlockX (Seq Deadlock Deadlock)) Empty,
    Alt Deadlock Empty,
    fwdAltDeadlockX (Alt Deadlock Empty),
    Empty
    ]
