{-# LANGUAGE BangPatterns #-}

import System.Environment
import Data.List

data Tree = Nil
          | White Tree
          | Black Tree
          | Split Tree Tree
          | Fail
          deriving Eq

data Possible = W | B | Both | Not deriving Eq

showPossible :: Possible -> String
showPossible B = "⬛"
showPossible W = "⬜"
showPossible Both = "？"
showPossible Not  = "✕"

instance Show Possible where
  show = showPossible

type Rule = [Integer]
type Rules = [Rule]
type Line  = [Possible]
type Board = [Line]

data Which = Row | Column deriving (Show, Eq)

data Signal a = Loop a | Continue a

instance Functor Signal where
  fmap f (Loop a) = Loop (f a)
  fmap f (Continue a) = Continue (f a)

isLoop :: Signal a -> Bool
isLoop (Loop a) = True
isLoop (Continue a) = False

cut :: Tree -> Tree
cut Fail                 = Fail
cut (White Fail)         = Fail
cut (Black Fail)         = Fail
cut (Split Fail Fail)    = Fail
cut (Split Fail success) = success
cut (Split success Fail) = success
cut success              = success


build :: Line -> Rule -> Line
build possible black =
  flat $ aux possible (toInteger $ length possible) black black
  where aux _ 0 [] _                  = Nil
        aux _ 0 _ (0:[])              = Nil
        aux _ 0 _  _                  = Fail
        aux (Not:ps) n xs ys          = aux (Both:ps) n xs ys
        aux (W:ps) n [] _             = cut $ White $ aux ps (n-1) [] []
        aux (B:ps) n [] _             = Fail
        aux (Both:ps) n [] _          = cut $ White $ aux ps (n-1) [] []
        aux (W:ps) n (_:xs) (0:ys)    = cut $ White $ aux ps (n-1) xs ys
        aux (B:ps) n (_:xs) (0:ys)    = Fail
        aux (Both:ps) n (_:xs) (0:ys) = cut $ White $ aux ps (n-1) xs ys
        aux (W:ps) n (x:xs) (y:ys)
          | x == y    = cut $ White $ aux ps (n-1) (x:xs) (y:ys)
          | otherwise = Fail
        aux (B:ps) n (x:xs) (y:ys)    = cut $ Black $ aux ps (n-1) (x:xs) (y-1:ys)
        aux (Both:ps) n (x:xs) (y:ys)
          | y > n            = Fail
          | n < x && x == y  = Fail
          | x > y            = cut $ Black $ aux ps (n-1) (x:xs) (y-1:ys)
          | x == y           = cut $ Split whiteBranch blackBranch
          where whiteBranch  = cut $ White $ aux ps (n-1) (x:xs) (y:ys)
                blackBranch  = cut $ Black $ aux ps (n-1) (x:xs) (y-1:ys)


flat :: Tree -> Line
flat Fail = []
flat Nil = []
flat (White tree) = W : flat tree
flat (Black tree) = B : flat tree
flat (Split white black) =
  zipWith (\a b -> if a /= b then Both else a) (flat white) (flat black)


merge :: [Possible] -> [Possible] -> [Possible]
merge [] []         = []
merge xs []         = replicate (length xs) Not
merge (x:xs) (y:ys) = aux x y : merge xs ys
  where aux W W = W
        aux B B = B
        aux W B = Not
        aux B W = Not
        aux Both other = other
        aux other Both = other
        aux Not _ = Not
        aux _ Not = Not


update :: (Rules, Rules) -> Which -> Integer -> Board -> Signal Board
update (rs,cs) which n ls
  | which == Row = updateLine n rs ls
  | which == Column = fmap transpose $ updateLine n cs $ transpose ls
  where optim line = sum $ zipWith (*) [1.. length line] $ map (fromEnum . (==B)) line
        updateLine 0 (r:rs) (l:ls) =
          let f = if (optim l) < (optim $ reverse l) then id else reverse
              newl = f $ build (f l) (f r) in
            if newl == l || Not `elem` l
            then Continue (l : ls)
            else Loop ((merge l $ build l r) : ls)
        updateLine n (r:rs) (l:ls) = fmap (l:) (updateLine (n-1) rs ls)


toPriority :: Rule -> Line -> Maybe Integer
toPriority [] _ = Just (-99)
toPriority ns line =
  if not (Both `elem` line)
  then Nothing
  else Just (p - ((s-1) * (g-1)))
  where p = (len - (sum $ intersperse 1 ns))
            * (len - (maximum ns))
            * (toInteger $ length $ intersperse 1 ns)
        len = toInteger $ length line
        (s,g) = (\lst ->
                   (sum $ map fst lst, toInteger $ length lst))
                $ filter (\(n,p) ->
                            p == B)
                $ map (\lst ->
                         (toInteger $ length lst, head lst))
                $ group line

toPriority' :: Rule -> Line -> Maybe Integer
toPriority' rule line =
  if not (Both `elem` line)
  then Nothing
  else Just (result - weight)
  where estComb len _ [] = 1
        estComb len [] (n:[]) = len - (n-1)
        estComb len [] (n:right) = count * (estComb len [n] right)
          where subLen = len - (1 + (sum $ intersperse 1 right))
                count  = subLen - (n-1)
        estComb len left (n:right) = ((space - (n-1))-2) * (estComb len (n:left) right)
          where subLen r = (1+) $ sum $ intersperse 1 r
                space = len - ((subLen left) + (subLen right))
        known = map length $ filter (head) $ group $ map (/=Both) line
        result = estComb (toInteger $ length line) [] rule
        weight = toInteger $ (sum known) * (length known)


makeRuleChain :: Rules -> Rules -> Board ->  [(Integer, Which, Integer)]
makeRuleChain rows columns board = sortBy (\(_,_,p1) (_,_,p2) ->
                                              compare p1 p2) (enrichRows ++ enrichColumns)
  where enrich ns b w =
          zipWith (\(i,n) l ->
                     (i, w, toPriority' n l))
          (zip [0 .. toInteger $ length ns] ns)
          b
        onlyJust = map (\(i,w,Just p) -> (i,w,p)) . filter (\(_,_,p) -> p /= Nothing)
        enrichRows = onlyJust $ enrich rows board Row
        enrichColumns = onlyJust $ enrich columns (transpose board) Column


buildInit :: [(Integer, Integer)] -> Int -> Int -> [[Possible]]
buildInit initial rowsN columnsN = groupN $ fillKnown flatInit board
  where board = replicate (columnsN*rowsN) Both
        flatInit = sort $ map (\(a,b) -> ((a-1)*toInteger columnsN)+(b-1)) initial
        fillKnown [] b = b
        fillKnown (0:xs) b = B : fillKnown (map pred xs) (tail b)
        fillKnown (x:xs) b = (head b) : fillKnown (x-1:(map pred xs)) (tail b)
        groupN [] = []
        groupN b = (take columnsN b) : groupN (drop columnsN b)


showIntermediate
  :: Bool -> Signal Board -> Integer -> Which -> Rules -> Rules -> Integer -> IO ()
showIntermediate True (Loop !board) i w rows columns n = do
  putStrLn $ mconcat [show n
                     , ": "
                     , show w
                     , " "
                     , show (i+1)
                     , " "
                     , show ((if w == Row then rows else columns) !! fromInteger i)
                     ]
  showBoard board
  putStrLn "Press ENTER to step forward..."
  getLine
  return ()
showIntermediate _ _ _ _ _ _ _ = return ()
          

solveStep :: Bool -> Rules -> Rules -> [(Integer, Integer)] -> Integer -> IO ()
solveStep step rows columns initial n = aux ruleChain (Loop board) n
  where board = buildInit initial (length rows) (length columns)
        ruleChain = makeRuleChain rows columns board
        ruleTup = (rows, columns)
        aux [] (Continue board) _ = showBoard board
        aux [] (Loop board) n =
          aux (makeRuleChain rows columns board) (Continue board) n
        aux ((i,w,_):decRuleChain) (Continue board) n = do
          let !newBoard = (update ruleTup w i board)
          case newBoard of
            (Loop b) -> do
              showIntermediate step newBoard i w rows columns n
              aux (makeRuleChain rows columns b) newBoard (succ n)
            (Continue b) ->
              aux decRuleChain newBoard n
        aux ((i,w,_):decRuleChain) (Loop board) n = do
          let !newBoard = (update ruleTup w i board)
          case newBoard of
            (Loop b) -> do
              showIntermediate step newBoard i w rows columns n
              aux (makeRuleChain rows columns b) newBoard (succ n)
            (Continue b) ->
              aux decRuleChain newBoard n


collectRules :: [String] -> ([[Integer]], [[Integer]], [(Integer, Integer)])
collectRules rules = (columns, rows, initial)
  where columns = toList $ select "columns:"
        rows =  toList $ select "rows:"
        initial = map (\[a,b] -> (a,b)) $ toList $ select "initial:"
        select section =
          takeWhile (\s -> [last s] /= ":") $ tail $ dropWhile (/=section) rules
        toList text =
          map (map (\n ->
                      read n :: Integer) . (\l ->
                                              if l == "."
                                              then []
                                              else words l)) text


showBoard :: Board -> IO ()
showBoard b = putStrLn $ intercalate "\n" $ map (mconcat . map show) b

main :: IO ()
main = do
  args <- getArgs
  case args of
    ["new"] -> do
      writeFile "nonogram-template.txt" "\ncolumns:\n\n\nrows:\n\n\ninitial:\n\n"
      putStrLn "Created nonogram-template.txt"
    ["new", filename] -> do
      writeFile filename "\ncolumns:\n\n\nrows:\n\n\ninitial:\n\n"
      putStrLn ("Created " ++ filename)
    ["example"] -> do
      writeFile "example.txt" "\ncolumns:\n7 2 1 1 7\n1 1 2 2 1 1\n1 3 1 3 1 3 1 3 1\n1 3 1 1 5 1 3 1\n1 3 1 1 4 1 3 1\n1 1 1 2 1 1\n7 1 1 1 1 1 7\n1 1 3\n2 1 2 1 8 2 1\n2 2 1 2 1 1 1 2\n1 7 3 2 1\n1 2 3 1 1 1 1 1\n4 1 1 2 6\n3 3 1 1 1 3 1\n1 2 5 2 2\n2 2 1 1 1 1 1 2 1\n1 3 3 2 1 8 1\n6 2 1\n7 1 4 1 1 3\n1 1 1 1 4\n1 3 1 3 7 1\n1 3 1 1 1 2 1 1 4\n1 3 1 4 3 3\n1 1 2 2 2 6 1\n7 1 3 2 1 1\n\n\nrows:\n7 3 1 1 7\n1 1 2 2 1 1\n1 3 1 3 1 1 3 1\n1 3 1 1 6 1 3 1\n1 3 1 5 2 1 3 1\n1 1 2 1 1\n7 1 1 1 1 1 7\n3 3\n1 2 3 1 1 3 1 1 2\n1 1 3 2 1 1\n4 1 4 2 1 2\n1 1 1 1 1 4 1 3\n2 1 1 1 2 5\n3 2 2 6 3 1\n1 9 1 1 2 1\n2 1 2 2 3 1\n3 1 1 1 1 5 1\n1 2 2 5\n7 1 2 1 1 1 3\n1 1 2 1 2 2 1\n1 3 1 4 5 1\n1 3 1 3 10 2\n1 3 1 1 6 6\n1 1 2 1 1 2\n7 2 1 2 5\n\n\ninitial:\n4 4\n4 5\n4 13\n4 14\n4 22\n9 7\n9 8\n9 11\n9 15\n9 16\n9 19\n17 7\n17 12\n17 17\n17 21\n22 4\n22 5\n22 10\n22 11\n22 16\n22 21\n22 22\n"
      putStrLn "Created example.txt based on GCHQ Christmas Puzzle"
    [filename] -> do
      rules <- readFile filename
      let (columns,rows,initial) = (collectRules . filter (/="") . lines) rules
      solveStep False rows columns initial 1
    ["step", filename] -> do
      rules <- readFile filename
      let (columns,rows,initial) = (collectRules . filter (/="") . lines) rules
      solveStep True rows columns initial 1
    _ -> do
      putStrLn "Usage information:"
      putStrLn "./exe filename      - run solver with rules from $filename"
      putStrLn "./exe step filename - as above but program pauses each iteration"
      putStrLn "./exe new           - build new template named nonogram-template.txt"
      putStrLn "./exe new filename  - build new template named $filename"
      putStrLn "./exe example       - outputs a template file with GCHQ puzzle example"
