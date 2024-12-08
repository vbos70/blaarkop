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
    | T ProcessGraph
    deriving (Show, Eq, Ord)

type Law = ProcessGraph -> ProcessGraph

x = Proc "x" (Seq (Act "a") x) -- X = a ; X

eval :: Law -> ProcessGraph -> ProcessGraph
eval l (Seq p1 p2) = Seq (eval l p1) (eval l p2) 
eval l (Alt p1 p2) = Alt (eval l p1) (eval l p2) 
eval l (Mrg p1 p2) = Mrg (eval l p1) (eval l p2) 
eval l (Lmr p1 p2) = Lmr (eval l p1) (eval l p2) 
eval l (Cmr p1 p2) = Lmr (eval l p1) (eval l p2) 
eval l (T p) = l p
eval l p = p -- otherwise

neg_eval :: Law -> ProcessGraph -> ProcessGraph
neg_eval l (Seq p1 p2) = Seq (neg_eval l p1) (neg_eval l p2) 
neg_eval l (Alt p1 p2) = Alt (neg_eval l p1) (neg_eval l p2) 
neg_eval l (Mrg p1 p2) = Mrg (neg_eval l p1) (neg_eval l p2) 
neg_eval l (Lmr p1 p2) = Lmr (neg_eval l p1) (neg_eval l p2) 
neg_eval l (Cmr p1 p2) = Cmr (neg_eval l p1) (neg_eval l p2) 
neg_eval l (T p) = p
neg_eval l p = p -- otherwise



-- delta ; x = x
fwdSeqDeadlockX :: Law
fwdSeqDeadlockX (Seq Deadlock x) = Deadlock
fwdSeqDeadlockX x = x

revSeqDeadlockX :: Law
revSeqDeadlockX x = Seq Deadlock x

-- empty ; x = x
fwdSeqEmptyX :: Law
fwdSeqEmptyX (Seq Empty x) = x
fwdSeqEmptyX x = x

revSeqEmptyX :: Law
revSeqEmptyX x = Seq Empty x

-- x ; empty = x
fwdSeqXEmpty :: Law
fwdSeqXEmpty (Seq x Empty) = x
fwdSeqXEmpty x = x

revSeqXEmpty :: Law
revSeqXEmpty x = Seq x Empty

-- (x ; y) ; z = x ; (y ; z)
fwdSeqSeq :: Law
fwdSeqSeq (Seq (Seq x y) z) = (Seq x (Seq y z)) 
fwdSeqSeq x = x

revSeqSeq :: Law
revSeqSeq (Seq x (Seq y z))  = (Seq (Seq x y) z)
revSeqSeq x = x

-- delta + x = x
fwdAltDeadlockX :: Law
fwdAltDeadlockX (Alt Deadlock x) = x
fwdAltDeadlockX x = x

revAltDeadlockX :: Law
revAltDeadlockX x = (Alt Deadlock x)

-- x + delta = x
fwdAltXDeadlock :: Law
fwdAltXDeadlock (Alt x Deadlock) = x
fwdAlXDeadlock x = x

revAltXDeadlock :: Law
revAltXDeadlock x = (Alt x Deadlock)

-- (x + y) + z = x + (y + z)
fwdAltAlt :: Law
fwdAltAlt (Alt (Alt x y) z) = (Alt x (Alt y z)) 
fwdAltAlt x = x

revAltAlt :: Law
revAltAlt (Alt x (Alt y z))  = (Alt (Alt x y) z)
revAltAlt x = x

-- (x + y) ; z = (x ; z) + (y ; z)
fwdSeqAltXYZ :: Law
fwdSeqAltXYZ (Seq (Alt x y) z) = Alt (Seq x z) (Seq y z)
fwdSeqAltXYZ x = x

revSeqAltXYZ :: Law
revSeqAltXYZ (Alt (Seq x z1) (Seq y z2))
    | z1 == z2 = Seq (Alt x y) z1
    | otherwise = Alt (Seq x z1) (Seq y z2)
revSeqAltXYZ x = x

step :: (Law, ProcessGraph) -> (Law, ProcessGraph) -> Bool
step (lx, px)  (ly, py)
    | eval lx px == py = True
    | px == neg_eval ly py = True
    | otherwise = False

calc:: [(Law, ProcessGraph)] -> Bool
calc [] = True
calc [x] = True
calc (x : y : xs)
    | step x y = calc (y : xs)
    | otherwise = False

noop :: Law
noop p = p

c1 = [
    (noop, Alt (Seq Deadlock (Seq Deadlock Empty)) Empty),
    (fwdSeqDeadlockX, Alt (Seq Deadlock (T (Seq Deadlock Empty))) Empty),
    (noop, Alt (Seq Deadlock Deadlock) Empty),
    (fwdSeqDeadlockX, Alt (T  (Seq Deadlock Deadlock)) Empty),
    (noop, Alt Deadlock Empty),
    (fwdAltDeadlockX, T (Alt Deadlock Empty)),
    (noop, Empty)
    ]
