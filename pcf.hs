data Type =
    NatType |
    BoolType |
    ArrowType Type Type |
    PairType Type Type |
    ListType Type |
    UnitType
    deriving (Eq)

instance Show Type where
    show NatType = "Nat"
    show BoolType = "Bool"
    show (ArrowType t1 t2) = "(" ++ (show t1) ++ " -> " ++ (show t2) ++ ")"
    show (PairType t1 t2) = "(" ++ (show t1) ++ ", " ++ (show t2) ++ ")"
    show (ListType t) = "[" ++ (show t) ++ "]"
    show UnitType = "Unit"

data Term =
    TVar Int |
    TLambda Type Term |
    TAppl Term Term |
    TTrue |
    TFalse |
    TIf Term Term Term |
    TZero |
    TSucc Term |
    TPred Term |
    TIsZero Term |
    TFix Term |
    TPair Term Term |
    TFirst Term |
    TSecond Term |
    TNil Type |
    TCons Term Term |
    TIsNil Term |
    THead Term |
    TTail Term |
    TUnit

isVal :: Term -> Bool
isVal (TLambda _ _) = True
isVal t | isNum t = True
isVal TTrue = True
isVal TFalse = True
isVal (TPair u v) = (isVal u) && (isVal v)
isVal (TNil _) = True
isVal (TCons u v) = (isVal u) && (isVal v)
isVal TUnit = True
isVal _ = False

isNum :: Term -> Bool
isNum TZero = True
isNum (TSucc u) = isNum u
isNum _ = False

toNum :: Term -> Int
toNum TZero = 0
toNum (TSucc x) = (toNum x) + 1

isList :: Term -> Bool
isList (TNil _) = True
isList (TCons _ _) = True
isList _ = False

toListAux :: Term -> String
toListAux (TNil _) = ""
toListAux (TCons u (TNil _)) = (show u)
toListAux (TCons u v) = (show u) ++ ", " ++ (toListAux v)

toList :: Term -> String
toList t = "[" ++ (toListAux t) ++ "]" 

instance Show Term where
    show x | (isNum x) = show (toNum x)
    show x | (isVal x) && (isList x) = toList x
    show (TVar x) = "`" ++ show x ++ "`"
    show (TLambda tp t) = "(L " ++ (show t) ++ ")"
    show (TAppl t1 t2) = "(" ++ (show t1) ++ " " ++ (show t2) ++ ")"
    show TTrue = "True"
    show TFalse = "False"
    show (TIf u v w) =
        "(If " ++ (show u) ++
        " then " ++ (show v) ++
        " else " ++ (show w) ++ ")"
    show TZero = "0"
    show (TSucc u) = "(succ " ++ (show u) ++ ")"
    show (TPred u) = "(pred " ++ (show u) ++ ")"
    show (TIsZero u) = "(0? " ++ (show u) ++ ")"
    show (TFix u) = "(fix " ++ (show u) ++ ")"
    show (TPair u v) = "(pair " ++ (show u) ++ " " ++ (show v) ++ ")"
    show (TFirst u) = "(fst " ++ (show u) ++ ")"
    show (TSecond u) = "(snd " ++ (show u) ++ ")"
    show (TNil t) = "Nil[" ++ (show t) ++ "]"
    show (TCons u v) = "(cons " ++ (show u) ++ " " ++ (show v) ++ ")"
    show (TIsNil u) = "(nil? " ++ (show u) ++ ")"
    show (THead u) = "(head " ++ (show u) ++ ")"
    show (TTail u) = "(tail " ++ (show u) ++ ")"
    show TUnit = "Unit"

typeOf :: Term -> [Type] -> Maybe Type
typeOf (TVar x) ctx =
    if (x < (length ctx))
        then (Just (ctx !! x))
        else Nothing
typeOf (TLambda tp t) ctx = do
    t1 <- typeOf t ([tp] ++ ctx)
    return (ArrowType tp t1)
typeOf (TAppl t1 t2) ctx = do
    tt1 <- typeOf t1 ctx
    case tt1 of
        (ArrowType u v) -> do
            tt2 <- typeOf t2 ctx
            if (u == tt2) then return v else Nothing
        _ -> Nothing
typeOf TTrue ctx = Just BoolType
typeOf TFalse ctx = Just BoolType
typeOf (TIf u v w) ctx = do
    tu <- typeOf u ctx
    if tu == BoolType
        then do
            tv <- typeOf v ctx
            tw <- typeOf w ctx
            if tv == tw then return tv else Nothing
        else Nothing
typeOf TZero ctx = Just NatType
typeOf (TSucc u) ctx = do
    t1 <- typeOf u ctx
    if t1 == NatType then return NatType else Nothing
typeOf (TPred u) ctx = do
    t1 <- typeOf u ctx
    if t1 == NatType then return NatType else Nothing
typeOf (TIsZero u) ctx = do
    t1 <- typeOf u ctx
    if t1 == NatType then return BoolType else Nothing
typeOf (TFix u) ctx = do
    t1 <- typeOf u ctx
    case t1 of
        (ArrowType u v) -> if u == v
            then case u of
                (ArrowType _ _) -> return u
                _ -> Nothing
            else Nothing
        _ -> Nothing
typeOf (TPair u v) ctx = do
    t1 <- typeOf u ctx
    t2 <- typeOf v ctx
    return (PairType t1 t2)
typeOf (TFirst u) ctx = do
    t1 <- typeOf u ctx
    case t1 of
        (PairType a b) -> return a
        _ -> Nothing
typeOf (TSecond u) ctx = do
    t1 <- typeOf u ctx
    case t1 of
        (PairType a b) -> return b
        _ -> Nothing
typeOf (TNil t) ctx = Just (ListType t)
typeOf (TCons u v) ctx = do
    t1 <- typeOf u ctx
    t2 <- typeOf v ctx
    if t2 == (ListType t1) then return t2 else Nothing
typeOf (TIsNil l) ctx = do
    t1 <- typeOf l ctx
    case t1 of
        (ListType _) -> return BoolType
        _ -> Nothing
typeOf (THead l) ctx = do
    t1 <- typeOf l ctx
    case t1 of
        (ListType aux) -> return aux
        _ -> Nothing
typeOf (TTail l) ctx = do
    t1 <- typeOf l ctx
    case t1 of
        (ListType _) -> return t1
        _ -> Nothing
typeOf TUnit ctx = Just UnitType

incr :: Int -> Int -> Term -> Term
incr d c (TVar x) = if (x < c) then (TVar x) else (TVar (x + d))
incr d c (TLambda tp t) = (TLambda tp (incr d (c + 1) t))
incr d c (TAppl t1 t2) = (TAppl (incr d c t1) (incr d c t2))
incr d c (TIf t1 t2 t3) = (TIf (incr d c t1) (incr d c t2) (incr d c t3))
incr d c (TSucc t1) = (TSucc (incr d c t1))
incr d c (TPred t1) = (TPred (incr d c t1))
incr d c (TIsZero t1) = (TIsZero (incr d c t1))
incr d c TZero = TZero
incr d c TTrue = TTrue
incr d c TFalse = TFalse
incr d c (TFix u) = TFix (incr d c u)
incr d c (TPair t1 t2) = (TPair (incr d c t1) (incr d c t2))
incr d c (TFirst u) = TFirst (incr d c u)
incr d c (TSecond u) = TSecond (incr d c u)
incr d c (TNil t) = (TNil t)
incr d c (TCons u v) = (TCons (incr d c u) (incr d c v))
incr d c (TIsNil t1) = (TIsNil (incr d c t1))
incr d c (THead t1) = (THead (incr d c t1))
incr d c (TTail t1) = (TTail (incr d c t1))
incr d c TUnit = TUnit

subs :: Int -> Term -> Term -> Term
subs j s (TVar k) = if (k == j) then s else (TVar k)
subs j s (TLambda tp t) = (TLambda tp (subs (j + 1) (incr 1 0 s) t))
subs j s (TAppl t1 t2) = (TAppl (subs j s t1) (subs j s t2))
subs j s (TIf t1 t2 t3) = (TIf (subs j s t1) (subs j s t2) (subs j s t3))
subs j s (TSucc t1) = (TSucc (subs j s t1))
subs j s (TPred t1) = (TPred (subs j s t1))
subs j s (TIsZero t1) = (TIsZero (subs j s t1))
subs j s TZero = TZero
subs j s TTrue = TTrue 
subs j s TFalse = TFalse
subs j s (TFix t1) = (TFix (subs j s t1))
subs j s (TPair t1 t2) = (TPair (subs j s t1) (subs j s t2))
subs j s (TFirst u) = TFirst (subs j s u)
subs j s (TSecond u) = TSecond (subs j s u)
subs j s (TNil t) = (TNil t)
subs j s (TCons u v) = (TCons (subs j s u) (subs j s v))
subs j s (TIsNil t1) = (TIsNil (subs j s t1))
subs j s (THead t1) = (THead (subs j s t1))
subs j s (TTail t1) = (TTail (subs j s t1))
subs j s TUnit = TUnit

eval :: Term -> Maybe Term
eval t | isVal t = Nothing
eval (TAppl (TLambda _ t1) t2) | (isVal t2) =
    Just (incr (-1) 0 (subs 0 (incr 1 0 t2) t1))
eval (TAppl t1 t2) | (isVal t1) = do
    aux <- eval t2
    return (TAppl t1 aux)
eval (TAppl t1 t2) = do
    aux <- eval t1
    return (TAppl aux t2)
eval (TIf TTrue u _) = Just u
eval (TIf TFalse _ v) = Just v
eval (TIf u v w) = do
    t <- eval u
    return (TIf t v w)
eval (TSucc u) = do
    t <- eval u
    return (TSucc t)
eval (TPred TZero) = Just TZero
eval (TPred (TSucc u)) | (isNum u) = Just u
eval (TPred u) = do
    t <- eval u
    return (TPred t)
eval (TIsZero TZero) = Just TTrue
eval (TIsZero u) | (isNum u) = Just TFalse
eval (TIsZero u) = do
    t <- eval u
    return (TIsZero t)
eval (TFix (TLambda tp u)) =
    Just (incr (-1) 0 (subs 0 (incr 1 0 (TFix (TLambda tp u))) u))
eval (TPair u v) | (isVal u) = do
    t2 <- eval v
    return (TPair u t2)
eval (TPair u v) = do
    t1 <- eval u
    return (TPair t1 v)
eval (TFirst u) | (isVal u) = do
    case u of
        (TPair p1 _) -> return p1
eval (TFirst u) = do
    t1 <- eval u
    return (TFirst t1)
eval (TSecond u) | (isVal u) = do
    case u of
        (TPair _ p2) -> return p2
eval (TSecond u) = do
    t1 <- eval u
    return (TSecond t1)
eval (TCons u v) | (isVal u) = do
    t1 <- eval v
    return (TCons u t1)
eval (TCons u v) = do
    t1 <- eval u
    return (TCons t1 v)
eval (TIsNil (TNil _)) = Just TTrue
eval (TIsNil u) | (isVal u) = Just TFalse
eval (TIsNil u) = do
    t1 <- eval u
    return (TIsNil t1)
eval (THead (TNil _)) = error "head of an empty list"
eval (THead (TCons u v)) | (isVal u) && (isVal v) = Just u
eval (THead u) = do
    t1 <- eval u
    return (THead t1)
eval (TTail (TNil _)) = error "tail of an empty list"
eval (TTail (TCons u v)) | (isVal u) && (isVal v) = Just v
eval (TTail u) = do
    t1 <- eval u
    return (TTail t1)

evalIt :: Term -> IO()
evalIt t = do
    case (eval t) of
        Just newT -> (evalIt newT)
        Nothing -> do
            print t

numToTerm :: Int -> Term
numToTerm 0 = TZero
numToTerm x = TSucc (numToTerm (x - 1))

intListToTerm :: [Int] -> Term
intListToTerm [] = (TNil NatType)
intListToTerm (x:xs) = (TCons (numToTerm x) (intListToTerm xs))

add :: Term
add =
    (TFix (TLambda (ArrowType NatType (ArrowType NatType NatType))
    (TLambda NatType (TLambda NatType
     (TIf
      (TIsZero (TVar 0))
      (TVar 1)
      (TAppl
       (TAppl
        (TVar 2)
        (TSucc (TVar 1)))
        (TPred (TVar 0))))))))

fib :: Term
fib =
    (TFix (TLambda (ArrowType NatType NatType)
    (TLambda NatType
     (TIf
      (TIsZero (TVar 0))
      TZero
      (TIf
       (TIsZero (TPred (TVar 0)))
       (TSucc TZero)
       (TAppl
        (TAppl
         add
         (TAppl (TVar 1) (TPred (TVar 0))))
         (TAppl (TVar 1) (TPred (TPred (TVar 0))))))))))
         
lmap :: Term
lmap =
    (TFix (TLambda
           (ArrowType (ArrowType NatType NatType)
                      (ArrowType (ListType NatType) (ListType NatType)))
    (TLambda (ArrowType NatType NatType)
    (TLambda (ListType NatType)
     (TIf
      (TIsNil (TVar 0))
      (TNil NatType)
      (TCons
       (TAppl (TVar 1) (THead (TVar 0)))
       (TAppl (TAppl (TVar 2) (TVar 1)) (TTail (TVar 0)))))))))

toEval :: Term
toEval =
    (TAppl (TAppl lmap fib) (intListToTerm [1, 2, 3, 4, 5, 6, 7, 8, 9, 10,
    11, 12, 13, 14, 15]))

main :: IO()
main = do
    print toEval
    t <- return (typeOf toEval [])
    print t
    if t == Nothing then return () else (evalIt toEval)
