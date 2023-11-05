import Distribution.Parsec (Parsec(parsec))
import Text.XHtml (p)
data ProcessGraph = 
    Deadlock
    | Empty
    | Act String
    | Proc String ProcessGraph
    | Seq ProcessGraph ProcessGraph
    | Alt ProcessGraph ProcessGraph
    | Mrg ProcessGraph ProcessGraph
    | LMr ProcessGraph ProcessGraph
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
