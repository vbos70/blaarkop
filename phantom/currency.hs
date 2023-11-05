data EUR

data DOLLAR

newtype Amount a = Amount Double
    deriving (Show, Eq, Ord) --, Num)


instance Num (Amount a) where
    Amount x + Amount y = Amount (x + y)
    Amount x * Amount y = Amount (x * y)
    abs (Amount x) = Amount (abs x)
    signum (Amount x) = if x<0 then -1 else 1
    fromInteger i = Amount (fromIntegral i)
    negate (Amount x) = Amount (negate x)

instance Fractional (Amount a) where
    fromRational r = Amount (fromRational r)
    (Amount x) / (Amount y) = Amount (x / y)


a :: Amount EUR
a = Amount 6.50

b :: Amount DOLLAR
b = Amount 6.50




dollar_rate = 1.1
euro_rate = 1.0




