-- open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Function
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Maybe using (Maybe; nothing; just)
open import Data.Nat as ℕ using (ℕ; suc; zero; _∸_; _≟_; _+_)
open import Data.List using (List; []; [_]; _++_; _∷_; map; zip; any; all; filter)
open import Data.Bool using (Bool; true; false; if_then_else_; _∧_; _∨_; T; not)
open import Relation.Binary.PropositionalEquality using (refl; _≡_)
open import Relation.Nullary using (¬_; yes; no)
open import Data.Empty using (⊥)
open import Data.Unit
open import Data.List.All as All using (All)
open import Data.List.Any as Any using (Any)

-- | utilities

_==_ : ℕ → ℕ → Bool
m == n with m ℕ.≟ n
... | yes _ = true
... | no  _ = false

_𝔹=_ : Bool → Bool → Bool
_𝔹=_ true true = true
_𝔹=_ false false = true
_𝔹=_ _     _     = false

-- indexing list with a eq function
!! : {A B : Set} → (A → A → Bool) → List (A × B) → A → Maybe B
!! _ [] p = nothing
!! eq ((a , b) ∷ as) p with eq a p
...| true = just b
...| _ = !! eq as p

_>_ : ℕ → ℕ → Bool
zero > zero = false
zero > suc _ = false
suc _ > zero = true
suc m > suc n = m > n

_<_ : ℕ → ℕ → Bool
zero < zero = false
zero < suc _ = true
suc _ < zero = false
suc a < suc b = a < b

-- | Membership

data _∈_ {A : Set}(x : A) : List A → Set where
  first : ∀ {xs}   → x ∈ x ∷ xs
  next  : ∀ {y xs} → x ∈ xs → x ∈ y ∷ xs

infix 4 _∈_

-- | Color

data Color : Set where
  white : Color
  black : Color

-- | Squares

data File : Set where
  A : File
  B : File
  C : File
  D : File
  E : File
  F : File
  G : File
  H : File

data Rank : Set where
  #1 : Rank
  #2 : Rank
  #3 : Rank
  #4 : Rank
  #5 : Rank
  #6 : Rank
  #7 : Rank
  #8 : Rank

Square = File × Rank

-- the king cannot castle if it passes through a square that would
-- put it in check

fileEq : File → File → Bool
fileEq A A = true
fileEq B B = true
fileEq C C = true
fileEq D D = true
fileEq E E = true
fileEq F F = true
fileEq G G = true
fileEq H H = true
fileEq _ _ = false

rankEq : Rank → Rank → Bool
rankEq #1 #1 = true
rankEq #2 #2 = true
rankEq #3 #3 = true
rankEq #4 #4 = true
rankEq #5 #5 = true
rankEq #6 #6 = true
rankEq #7 #7 = true
rankEq #8 #8 = true
rankEq _  _  = false

rankIs : Rank → Square → Bool
rankIs r (a , b) = rankEq r b

sqEq : Maybe Square → Square → Bool
sqEq (just (a , b)) (c , d) = fileEq a c ∧ rankEq b d
sqEq _ _ = false

-- i tried to avoid casting to naturals but some things are just easier with it
fileToℕ : File → ℕ
fileToℕ A = 1
fileToℕ B = 2
fileToℕ C = 3
fileToℕ D = 4
fileToℕ E = 5
fileToℕ F = 6
fileToℕ G = 7
fileToℕ H = 8

ℕtoFile : ℕ → File
ℕtoFile zero = A
ℕtoFile 1 = A
ℕtoFile 2 = B
ℕtoFile 3 = C
ℕtoFile 4 = D
ℕtoFile 5 = E
ℕtoFile 6 = F
ℕtoFile 7 = G
ℕtoFile 8 = H
ℕtoFile _ = H

rankToℕ : Rank → ℕ
rankToℕ #1 = 1
rankToℕ #2 = 2
rankToℕ #3 = 3
rankToℕ #4 = 4
rankToℕ #5 = 5
rankToℕ #6 = 6
rankToℕ #7 = 7
rankToℕ #8 = 8

ℕtoRank : ℕ → Rank
ℕtoRank 1 = #1
ℕtoRank 2 = #2
ℕtoRank 3 = #3
ℕtoRank 4 = #4
ℕtoRank 5 = #5
ℕtoRank 6 = #6
ℕtoRank 7 = #7
ℕtoRank 8 = #8
ℕtoRank _ = #8

file : Square → ℕ
file (a , b) = fileToℕ a

rank : Square → ℕ
rank (_ , b) = rankToℕ b

isValid : ℕ × ℕ → Bool
isValid (a , b) =
  a > 0 ∧ a < 9 ∧ b > 0 ∧ b < 9
  
-- enumerating the squares around a square. used for checking if the
-- king is in checkmate
sqsAround : Square → List Square
sqsAround (a' , b') =
  let a = fileToℕ a'
      b = rankToℕ b'
      sqs = (a + 1 , b) ∷ (a ∸ 1 , b) ∷ (a , b + 1) ∷ (a , b ∸ 1) ∷ []
  in map (λ{ (c , d) → ℕtoFile c , ℕtoRank d })
         (filter isValid sqs)

-- | is this square relative to that one or that one to this?
-- | how many columns or rows away is a square

columnsAway : Square → Square → ℕ
columnsAway (a , _) (b , _) =
  let a' = fileToℕ a
      b' = fileToℕ b
  in if a' > b' then a' ∸ b'
                else b' ∸ a'
                 
aa = columnsAway (A , #1) (B , #1) 
ab = columnsAway (A , #1) (A , #1)
ac = columnsAway (A , #1) (H , #1)

rowsAway : Square → Square → ℕ
rowsAway (_ , a') (_ , b') =
  let a = rankToℕ a'
      b = rankToℕ b'
  in if a > b then a ∸ b
           else b ∸ a

-- | helpers for enumerating squares *between* squares

enumBetweenℕ₁ : ℕ → ℕ → List ℕ
enumBetweenℕ₁ a zero    = []
enumBetweenℕ₁ a (suc b) =
   if a == b then []
   else b ∷ enumBetweenℕ₁ a b

enumBetweenℕ : ℕ → ℕ → List ℕ
enumBetweenℕ a b =
  if a > b
  then enumBetweenℕ₁ b a
  else enumBetweenℕ₁ a b

bc : enumBetweenℕ 4 8 ≡ (7 ∷ 6 ∷ 5 ∷ [])
bc = refl
be = enumBetweenℕ 8 4
bd = enumBetweenℕ  1 4
bf = enumBetweenℕ 4 1

enumBetweenRanks : Rank → Rank → List Rank
enumBetweenRanks a b =
  let a' = rankToℕ a
      b' = rankToℕ b
  in map ℕtoRank (enumBetweenℕ a' b')

enumBetweenFiles : File → File → List File
enumBetweenFiles a b =
  let a' = fileToℕ a
      b' = fileToℕ b
  in map ℕtoFile (enumBetweenℕ a' b')

-- | is it straight, diagonal or horsey

isStraight : Square → Square → Bool
isStraight (a , b) (c , d) = fileEq a c ∨ rankEq b d

isDiagonal : Square → Square → Bool
isDiagonal a b =
  (columnsAway a b > 0 ∧ rowsAway a b > 0) ∧
  (columnsAway a b == rowsAway a b)

isHorseyMove : Square → Square → Bool
isHorseyMove a b = 
  (columnsAway a b == 2 ∧ rowsAway a b == 1) ∨
  (columnsAway a b == 1 ∧ rowsAway a b == 2)

oneSquareAway : Square → Square → Bool
oneSquareAway a b = 
  (columnsAway a b == 1 ∧ rowsAway a b == 0) ∨
  (columnsAway a b == 0 ∧ rowsAway a b == 1) ∨
  (columnsAway a b == 1 ∧ rowsAway a b == 1)

enumStraight : (sq sq₁ : Square) → T (isStraight sq sq₁) → List Square
enumStraight (a , b) (c , d) _ =
  if fileEq a c -- we're in a column
  then map (a ,_) (enumBetweenRanks b d)
  else map (_, b) (enumBetweenFiles a c)

-- | "unit tests" for enumSquaresStraight

ba : List Square
ba = enumStraight (A , #4) (A , #8) tt

bb : List Square
bb = enumStraight (A , #4) (A , #1) tt 

bg : List Square
bg = enumStraight (A , #5) (D , #5) tt

-- | enumerating squares diagonally

enumDiagonal : (sq sq₁ : Square) → T (isDiagonal sq sq₁) → List Square
enumDiagonal (a , b) (c , d) _ = 
  let rs = enumBetweenRanks b d
      fs = enumBetweenFiles a c
  in zip fs rs

oneFileHigher : Square → Square → Bool
oneFileHigher s q = (file s ∸ file q) == 1

oneFileLower : Square → Square → Bool
oneFileLower s q = (file q ∸ file s) == 1
    
oneRankHigher : Square → Square → Bool
oneRankHigher s q = (rank s ∸ rank q) == 1

oneRankLower : Square → Square → Bool
oneRankLower s q = (rank q ∸ rank s) == 1

sameFile : Square → Square → Bool
sameFile (a , b) (c , d) = fileEq a c

sameRank : Square → Square → Bool
sameRank (a , b) (c , d) = rankEq b d

twoFilesLower : Square → Square → Bool
twoFilesLower s q = (file q ∸ file s) == 2

twoFilesHigher : Square → Square → Bool
twoFilesHigher s q = (file s ∸ file q) == 2

twoRanksLower : Square → Square → Bool
twoRanksLower s q = (rank q ∸ rank s) == 2

twoRanksHigher : Square → Square → Bool
twoRanksHigher s q = (rank s ∸ rank q) == 2

north : Square → Square → Bool
north s q = sameFile s q ∧ oneRankHigher s q

east : Square → Square → Bool
east s q = sameRank s q ∧ oneFileHigher s q

south : Square → Square → Bool
south s q = sameFile s q ∧ oneRankLower s q

west : Square → Square → Bool
west s q = sameRank s q ∧ oneFileLower s q

northeast : Square → Square → Bool
northeast s q = oneFileHigher s q ∧ oneRankHigher s q

northwest : Square → Square → Bool
northwest s q = oneFileLower s q ∧ oneRankHigher s q

southeast : Square → Square → Bool
southeast s q = oneFileHigher s q ∧ oneRankLower s q

southwest : Square → Square → Bool
southwest s q = oneFileLower s q ∧ oneRankLower s q

atTopOrBottom : Square → Bool
atTopOrBottom (_ , #1) = true
atTopOrBottom (_ , #8) = true
atTopOrBottom _ = false

-- | is a square relative to another or is that one relative to this one?
    
-- | Pieces

-- king's rook or queens, kings knight or queens , etc
data Which : Set where
  k : Which
  q : Which
 
data WhichPawn : Set where
  p1 : WhichPawn
  p2 : WhichPawn
  p3 : WhichPawn
  p4 : WhichPawn
  p5 : WhichPawn
  p6 : WhichPawn
  p7 : WhichPawn
  p8 : WhichPawn

data Piece : Set where
  king   : Piece
  queen  : Piece
  bishop : Which → Piece
  knight : Which → Piece
  rook   : Which → Piece
  pawn   : WhichPawn → Piece

pieceEq : Piece → Piece → Bool
pieceEq king king = true
pieceEq queen queen = true
pieceEq (bishop k)  (bishop k) = true
pieceEq (bishop q) (bishop q) = true
pieceEq (knight k)  (knight k) = true
pieceEq (knight q) (knight q) = true
pieceEq (rook   k)  (rook k) = true
pieceEq (rook   q) (rook q) = true
pieceEq (pawn p1) (pawn p1) = true
pieceEq (pawn p2) (pawn p2) = true
pieceEq (pawn p3) (pawn p3) = true
pieceEq (pawn p4) (pawn p4) = true
pieceEq (pawn p5) (pawn p5) = true
pieceEq (pawn p6) (pawn p6) = true
pieceEq (pawn p7) (pawn p7) = true
pieceEq (pawn p8) (pawn p8) = true
pieceEq _     _  = false

whichPawnEq : WhichPawn → WhichPawn → Bool
whichPawnEq p1 p1 = true
whichPawnEq p2 p2 = true
whichPawnEq p3 p3 = true
whichPawnEq p4 p4 = true
whichPawnEq p5 p5 = true
whichPawnEq p6 p6 = true
whichPawnEq p7 p7 = true
whichPawnEq p8 p8 = true
whichPawnEq _  _  = false

-- | Side, information about the pieces of each color

record Side : Set where
  field
    pieces       : List (Piece × Maybe Square)
    kMoved       : Bool -- did the king move?
    qrMoved      : Bool -- either of the rooks moved?
    krMoved      : Bool
    pawnHasMoved : List (WhichPawn × Bool) -- can the pawn en passant?
    pawnPromotes : List (WhichPawn × Maybe Piece) -- which piece are you now?
    
open Side

-- | BoardArrangement

record BoardArrangement : Set where
  field
    whiteSide : Side
    blackSide : Side
    whosTurn : Color

open BoardArrangement

lcastlePassesThroughSquare : BoardArrangement → Square
lcastlePassesThroughSquare b =
  case whosTurn b of
  λ{ white → (C , #1)
   ; black → (C , #8)
   }

scastlePassesThroughSquare : BoardArrangement → Square
scastlePassesThroughSquare b =
  case whosTurn b of
  λ{ white → (G , #1)
   ; black → (G , #8)
   }

-- | all of the pieces
allPieces : BoardArrangement → List (Piece × Maybe Square)
allPieces record { whiteSide = w
                 ; blackSide = b
                 } =
  pieces w ++ pieces b

turnSide : BoardArrangement → Side
turnSide b =
  case whosTurn b of
  λ{ white → whiteSide b
   ; black → blackSide b
   }
   
-- | finding squares

sqOf : Piece × Maybe Square → Maybe Square
sqOf (a , b) = b

sqsOfAllPieces = map sqOf ∘ allPieces

sqOfPiece : BoardArrangement → Piece → Maybe Square
sqOfPiece b p =
  let wps = pieces (whiteSide b)
      bps = pieces (blackSide b)
  in case whosTurn b of
  λ{ white → case !! pieceEq wps p of
              λ{ (just sq) → sq
               ; nothing → nothing
               }
   ; black → case !! pieceEq bps p of
              λ{ (just sq) → sq
               ; nothing → nothing
               }
   }

sqOfOpponentPiece : BoardArrangement → Piece → Maybe Square
sqOfOpponentPiece b p =
  let wps = pieces (whiteSide b)
      bps = pieces (blackSide b)
  in case whosTurn b of
  λ{ white → case !! pieceEq bps p of
              λ{ (just sq) → sq
               ; nothing → nothing
               }
   ; black → case !! pieceEq wps p of
              λ{ (just sq) → sq
               ; nothing → nothing
               }
   }

sqsOfOpponentPieces : BoardArrangement → List (Maybe Square)
sqsOfOpponentPieces b = 
  case whosTurn b of
  λ{ white → map sqOf (pieces (blackSide b))
   ; black → map sqOf (pieces (whiteSide b))
   }
 
sqsOfFriendlyPieces : BoardArrangement → List (Maybe Square)
sqsOfFriendlyPieces b =
  case whosTurn b of
  λ{ white → map sqOf (pieces (whiteSide b))
   ; black → map sqOf (pieces (blackSide b))
   }

-- | altering pieces 

updatePiece : List (Piece × Maybe Square) → Piece → Maybe Square → List (Piece × Maybe Square)
updatePiece [] p sq = []
updatePiece ((x , y) ∷ xs) p sq with pieceEq x p
...| true = (x , sq) ∷ xs
...| false = (x , y) ∷ updatePiece xs p sq

updateSide : Side → List (Piece × Maybe Square) → Side
updateSide s l = record s {pieces = l}

mvPiece : BoardArrangement → Piece → Square → BoardArrangement
mvPiece b p sq =
  let wps = pieces (whiteSide b)
      bps = pieces (blackSide b)
  in case whosTurn b of
     λ{ white → record b {
         whiteSide =
           updateSide (whiteSide b) (updatePiece wps p (just sq)) }
      ; black → record b {
          blackSide =
            updateSide (blackSide b) (updatePiece bps p (just sq)) }
      }
   
removePiece : BoardArrangement → Piece → BoardArrangement
removePiece b p =
  let wps = pieces (whiteSide b)
      bps = pieces (blackSide b)
  in case whosTurn b of
     λ{ white → record b {
          blackSide =
            updateSide (blackSide b) (updatePiece bps p nothing)}
      ; black → record b {
          whiteSide =
            updateSide (whiteSide b) (updatePiece wps p nothing)}
      }

-- | helper for whoHasSquare

!!! : {A B : Set} → (Maybe B → B → Bool) → List (A × Maybe B) → B → Maybe A
!!! eq [] b = nothing
!!! eq ((y , x) ∷ xs) b with eq x b
...| true = just y 
...| false = !!! eq xs b

-- | helper for capturePiece

whoHasSquare : BoardArrangement → Square → Maybe Piece
whoHasSquare b s =
  let wps = pieces (whiteSide b)
      bps = pieces (blackSide b)
  in case whosTurn b of
     λ{ white → !!! sqEq wps s
      ; black → !!! sqEq bps s
      }
   
capturePiece : BoardArrangement → Piece → Square → BoardArrangement
capturePiece b p sq =
  let b' = mvPiece b p sq
  in case whoHasSquare b sq of
     λ{ (just p) → removePiece b' p
      ; nothing → b'
      }

-- | short and long castles

lcastle : BoardArrangement → BoardArrangement
lcastle b =
  case whosTurn b of
  λ{ white →
       let b' = mvPiece b king (C , #1)
       in mvPiece b' (rook q) (D , #1)
   ; black → 
       let b' = mvPiece b king (C , #8)
       in mvPiece b' (rook q) (D , #8)
   }

scastle : BoardArrangement → BoardArrangement
scastle b = 
  case whosTurn b of
  λ{ white →
       let b' = mvPiece b king (G , #1)
       in mvPiece b' (rook k) (F , #1)
   ; black →
       let b' = mvPiece b king (G , #8)
       in mvPiece b' (rook k) (F , #8)
   }

-- | helper for promotePawn₁

setPawn : List (WhichPawn × Maybe Piece) → WhichPawn → Piece → List (WhichPawn × Maybe Piece)
setPawn [] _ _ = []
setPawn ((ws , a) ∷ pcs) wp p with whichPawnEq ws wp
...| true = (ws , just p) ∷ pcs
...| false = (ws , a) ∷ setPawn pcs wp p

-- | helper for promotePawn

promotePawn₁ : Side → WhichPawn → Piece → Side
promotePawn₁ s wp p =
  let proms = pawnPromotes s
  in record s { pawnPromotes = setPawn proms wp p }
  
promotePawn : BoardArrangement → WhichPawn → Piece →  BoardArrangement
promotePawn b wp p =
  let ws = whiteSide b
      bs = blackSide b
  in case whosTurn b of
     λ{ white → 
          record b { whiteSide = promotePawn₁ ws wp p }
      ; black →
          record b { blackSide = promotePawn₁ bs wp p }
      }

pawnMoved₁ : WhichPawn → List (WhichPawn × Bool) → Bool
pawnMoved₁ wp [] = false
pawnMoved₁ wp ((wp₁ , b) ∷ cs) with whichPawnEq wp wp₁
...| true = b
...| false = pawnMoved₁ wp cs

pawnMoved : BoardArrangement → WhichPawn → Bool
pawnMoved b wp =
  case whosTurn b of
  λ{ white → pawnMoved₁ wp (pawnHasMoved (whiteSide b))
   ; black → pawnMoved₁ wp (pawnHasMoved (blackSide b))
   }
   
markPawn₁ : WhichPawn → List (WhichPawn × Bool) → List (WhichPawn × Bool)
markPawn₁ wp [] = []
markPawn₁ wp ((wp₁ , b) ∷ cs) with whichPawnEq wp wp₁
...| true = (wp , true) ∷ cs
...| false = (wp₁ , b) ∷ markPawn₁ wp cs

markPawnMoved : WhichPawn → BoardArrangement → BoardArrangement
markPawnMoved wp b =
  let ws = whiteSide b
      bs = blackSide b
  in case whosTurn b of
     λ{ white →
          record b { whiteSide =
            record ws {
              pawnHasMoved = markPawn₁ wp (pawnHasMoved ws)}}
      ; black →
          record b { blackSide =
            record bs {
              pawnHasMoved = markPawn₁ wp (pawnHasMoved bs)}}
      }

movePawn : BoardArrangement → WhichPawn → Square → BoardArrangement
movePawn b wp s =
  markPawnMoved wp (mvPiece b (pawn wp) s)

capturePawn : BoardArrangement → WhichPawn → Square → BoardArrangement
capturePawn b wp s =
  markPawnMoved wp (capturePiece b (pawn wp) s)

doEnPassant : BoardArrangement → WhichPawn → Square → Square → BoardArrangement
doEnPassant b wp sq sq₁ = 
  let b' = mvPiece b (pawn wp) sq
  in case whoHasSquare b sq₁ of -- cheating
     λ{ (just (pawn p)) → removePiece b' (pawn p)
      ; _ → b'
      }

markKingMoved : BoardArrangement → BoardArrangement 
markKingMoved b =
  let ws = whiteSide b
      bs = blackSide b
  in case whosTurn b of
     λ{ white → record b { whiteSide = record ws { kMoved = true }}
      ; black → record b { blackSide = record bs { kMoved = true }}
      }

markRookMoved : Which → BoardArrangement → BoardArrangement
markRookMoved w b =
  let ws = whiteSide b
      bs = blackSide b
  in case w , whosTurn b of
     λ{ (q , white) →
           record b {whiteSide = record ws { qrMoved = true }}
      ; (q , black) →
           record b {blackSide = record bs { qrMoved = true }}
      ; (k , white) →
           record b {whiteSide = record ws { krMoved = true }}
      ; (k , black) →
           record b {blackSide = record bs { krMoved = true }}
      }
  
data IsPromoted : WhichPawn → Piece → WhichPawn × Maybe Piece → Set where
  isPromoted : ∀{wp p entry}
    → wp ≡ proj₁ entry
    → just p ≡ proj₂ entry
    → IsPromoted wp p entry
    
data Promoted : BoardArrangement → WhichPawn → Piece → Set where
  isPromW : ∀{b wp p}
    → whosTurn b ≡ white
    → Any (IsPromoted wp p) (pawnPromotes (whiteSide b))
    → Promoted b wp p
    
  isPromB : ∀{b wp p}
    → whosTurn b ≡ black
    → Any (IsPromoted wp p) (pawnPromotes (blackSide b))
    → Promoted b wp p

data IsNotProm : WhichPawn → WhichPawn × Maybe Piece → Set where
  isNotProm : ∀{wp entry}
    → wp ≡ proj₁ entry
    → nothing ≡ proj₂ entry
    → IsNotProm wp entry

data NotPromoted : BoardArrangement → WhichPawn → Set where
  isNotPromotedW : ∀{b wp}
    → whosTurn b ≡ white
    → Any (IsNotProm wp) (pawnPromotes (whiteSide b))
    → NotPromoted b wp

  isNotPromotedB : ∀{b wp}
    → whosTurn b ≡ black
    → Any (IsNotProm wp) (pawnPromotes (blackSide b))
    → NotPromoted b wp

-- the movement of pawns

oneSquareForward : BoardArrangement → Square → Square → Bool
oneSquareForward b s sq =
  case whosTurn b of
  λ{ white → sameFile s sq ∧ oneRankHigher s sq
   ; black → sameFile s sq ∧ oneRankLower s sq
   }

isCaptureMove : BoardArrangement → Square → Square → Bool
isCaptureMove b s sq =
  case whosTurn b of
  λ{ white → northeast s sq ∨ northwest s sq
   ; black → southeast s sq ∨ southwest s sq
   }


-- | the occupation of little bits of land

data Occupied : BoardArrangement → Square → Set where
  occupied : ∀{sq b}
    → just sq ∈ sqsOfAllPieces b → Occupied b sq

data OccupiedWith : BoardArrangement → Piece → Square → Set where
  occWith : ∀{b p sq}
    → just sq ≡ sqOfPiece b p
    → OccupiedWith b p sq

data OccupiedWithOpponentPiece : BoardArrangement → Piece → Square → Set where
  occWithOpponentPiece : ∀{b p sq}
    → just sq ≡ sqOfOpponentPiece b p
    → OccupiedWithOpponentPiece b p sq
    
data OccupiedByOpponent : BoardArrangement → Square → Set where
  occOpponent : ∀{b sq}
    → just sq ∈ sqsOfOpponentPieces b
    → OccupiedByOpponent b sq

data OccupiedByFriendly : BoardArrangement → Square → Set where
  occFriendly : ∀{b sq}
    → just sq ∈ sqsOfFriendlyPieces b
    → OccupiedByFriendly b sq
    
data NotOccupied : BoardArrangement → List Square → Set where
  notOccEmpty : ∀{b} → NotOccupied b []
  notOccStep : ∀{b sq sqs}
    → ¬ Occupied b sq
    → NotOccupied b sqs
    → NotOccupied b (sq ∷ sqs)

data NotOccupiedSCastle : BoardArrangement → Set where
  notOccSCastleW : ∀{b}
    → (whosTurn b ≡ white)
    → ¬ Occupied b (G , #1)
    → ¬ Occupied b (F , #1)
    → NotOccupiedSCastle b

  notOccSCastleB : ∀{b}
    → (whosTurn b ≡ black)
    → ¬ Occupied b (G , #8)
    → ¬ Occupied b (F , #8)
    → NotOccupiedSCastle b

data NotOccupiedLCastle : BoardArrangement → Set where
  notOccLCastleW : ∀{b}
    → (whosTurn b ≡ white)
    → ¬ Occupied b (B , #1)
    → ¬ Occupied b (C , #1)
    → ¬ Occupied b (D , #1)
    → NotOccupiedLCastle b

  notOccLCastleB : ∀{b}
    → (whosTurn b ≡ black)
    → ¬ Occupied b (B , #8)
    → ¬ Occupied b (C , #8)
    → ¬ Occupied b (D , #8)
    → NotOccupiedLCastle b

-- sq is start, sq₁ is dest, sq₂ is opponent pawn
data IsEnPassantMove : BoardArrangement → Square → Square → Square → Set where
  isEnPassantMoveW : ∀{whichp b sq sq₁ sq₂}
    → T (rankEq #5 (proj₂ sq))
    → OccupiedWithOpponentPiece b (pawn whichp) sq₂
    → T (fileEq (proj₁ sq₁) (proj₁ sq₂))
    → T (oneRankHigher sq₁ sq₂)
    → IsEnPassantMove b sq sq₁ sq₂

  isEnPassantMoveB : ∀{whichp b sq sq₁ sq₂}
    → T (rankEq #4 (proj₂ sq))
    → OccupiedWithOpponentPiece b (pawn whichp) sq₂
    → T (fileEq (proj₁ sq₁) (proj₁ sq₂))
    → T (oneRankLower sq₁ sq₂)
    → IsEnPassantMove b sq sq₁ sq₂

-- | kings and their being in check

data CanBeAttacked : BoardArrangement → Square → Set where
  canAttackKing : ∀{b sq ksq}
    → OccupiedWithOpponentPiece b king ksq
    → T (oneSquareAway sq ksq)
    → CanBeAttacked b sq

  canAttackQueenStraight : ∀{b sq qsq}
    → OccupiedWithOpponentPiece b queen qsq
    → (p : T (isStraight sq qsq))
    → NotOccupied b (enumStraight sq qsq p)
    → CanBeAttacked b sq
    
  canAttackQueenDiagonal : ∀{b sq qsq}
    → OccupiedWithOpponentPiece b queen qsq
    → (p : T (isDiagonal sq qsq))
    → NotOccupied b (enumDiagonal sq qsq p)
    → CanBeAttacked b sq

  canAttackBishop : ∀{whichb b sq bsq }
    → OccupiedWithOpponentPiece b (bishop whichb) bsq
    → (p : T (isDiagonal sq bsq))
    → NotOccupied b (enumDiagonal sq bsq p)
    → CanBeAttacked b sq

  canAttackKnight : ∀{whichk b sq ksq}
    → OccupiedWithOpponentPiece b (knight whichk) ksq
    → T (isHorseyMove sq ksq)
    → CanBeAttacked b sq

  canAttackRook : ∀{whichr b sq rsq}
    → OccupiedWithOpponentPiece b (rook whichr) rsq
    → (p : T (isStraight sq rsq))
    → NotOccupied b (enumStraight sq rsq p)
    → CanBeAttacked b sq

  canAttackPawn : ∀{whichp b sq psq}
    → OccupiedWithOpponentPiece b (pawn whichp) psq
    → T (isCaptureMove b sq psq)
    → CanBeAttacked b sq

data Check : BoardArrangement → Set where
  check : ∀{b sq}
    → OccupiedWith b king sq
    → CanBeAttacked b sq
    → Check b

data BadSquare : BoardArrangement → Square → Set where
  attackIsBad : ∀{b sq}
   → CanBeAttacked b sq
   → BadSquare b sq

  occFriendlyIsBad : ∀{b sq}
    → OccupiedByFriendly b sq
    → BadSquare b sq

data Checkmate : BoardArrangement → Set where
  checkmate : ∀{b sq}
    → OccupiedWith b king sq
    → CanBeAttacked b sq
    → All (BadSquare b) (sqsAround sq)
    → Checkmate b

-- pseudo algebraic notation for moves

data Move : Set where
  0-0-0 : Move
  0-0 : Move
  ep : WhichPawn → Square → Move
  p= : WhichPawn → Piece → Move
  K : Square → Move
  Q : Square → Move
  B : Which → Square → Move
  R : Which → Square → Move
  N : Which → Square → Move
  P : WhichPawn → Square → Move
  Kx : Square → Move
  Qx : Square → Move
  Bx : Which → Square → Move
  Rx : Which → Square → Move
  Nx : Which → Square → Move
  Px : WhichPawn → Square → Move
  
-- | The Moves

-- the second board is the result of the move on the first board 
-- or at least that was the intention
-- according to the Game type b is the next board and b₁ is the
-- old board. I don't understand why the Game type doesn't behave
-- intuitively
data IsMove : Move → BoardArrangement → BoardArrangement → Set where
  mvKing : ∀{m b₁ sq sq₁}
    → (K sq₁) ≡ m
    → (b : BoardArrangement)
    → ¬ Checkmate b
    → OccupiedWith b king sq
    → T (oneSquareAway sq sq₁)
    → ¬ Occupied b sq₁
    → b₁ ≡ markKingMoved (mvPiece b king sq₁)
    → ¬ Check b₁
    → IsMove m b b₁

  capKing : ∀{m b₁ sq sq₁}
    → (Kx sq₁) ≡ m
    → (b : BoardArrangement)
    → ¬ Checkmate b
    → OccupiedWith b king sq
    → T (oneSquareAway sq sq₁)
    → OccupiedByOpponent b sq₁
    → b₁ ≡ capturePiece b king sq₁
    → ¬ Check b₁
    → IsMove m b b₁

  longCastle : ∀{b₁ m}
    → 0-0-0 ≡ m
    → (b : BoardArrangement)
    → ¬ Checkmate b
    → ¬ T (kMoved (turnSide b))
    → ¬ T (qrMoved (turnSide b))
    → ¬ (CanBeAttacked b (lcastlePassesThroughSquare b))
    → NotOccupiedLCastle b 
    → b₁ ≡ lcastle b
    → ¬ Check b₁
    → IsMove 0-0-0 b b₁

  shortCastle : ∀{b₁ m}
    → 0-0 ≡ m
    → (b : BoardArrangement)
    → ¬ Checkmate b
    → ¬ T (kMoved (turnSide b))
    → ¬ T (krMoved (turnSide b))
    → ¬ CanBeAttacked b (scastlePassesThroughSquare b)
    → NotOccupiedSCastle b
    → b₁ ≡ scastle b
    → ¬ Check b₁
    → IsMove 0-0 b b₁
    
  mvQueenStraight : ∀{b₁ sq sq₁ m}
    → (Q sq₁) ≡ m
    → (b : BoardArrangement)
    → ¬ Check b
    → OccupiedWith b queen sq
    → (p : T (isStraight sq sq₁))
    → NotOccupied b (enumStraight sq sq₁ p)
    → ¬ Occupied b sq₁
    → b₁ ≡ mvPiece b queen sq₁
    → ¬ Check b₁
    → IsMove m b b₁

  capQueenStraight : ∀{b₁ m sq sq₁}
    → (Qx sq₁) ≡ m
    → (b : BoardArrangement)
    → ¬ Check b
    → OccupiedWith b queen sq
    → (p : T (isStraight sq sq₁))
    → NotOccupied b (enumStraight sq sq₁ p)
    → OccupiedByOpponent b sq₁
    → b₁ ≡ capturePiece b queen sq₁
    → ¬ Check b₁
    → IsMove m b b₁

  mvQueenDiagonal : ∀{b₁ m sq sq₁}
    → (Q sq₁) ≡ m
    → (b : BoardArrangement)
    → ¬ Check b
    → OccupiedWith b queen sq
    → (p : T (isDiagonal sq sq₁))
    → NotOccupied b (enumDiagonal sq sq₁ p)
    → ¬ Occupied b sq₁
    → b₁ ≡ mvPiece b queen sq₁
    → ¬ Check b₁
    → IsMove m b b₁

  capQueenDiagonal : ∀{b₁ m sq sq₁}
    → (Qx sq₁) ≡ m
    → (b : BoardArrangement)
    → ¬ Check b
    → OccupiedWith b queen sq
    → (p : T (isDiagonal sq sq₁))
    → NotOccupied b (enumDiagonal sq sq₁ p) 
    → OccupiedByOpponent b sq₁
    → b₁ ≡ capturePiece b queen sq₁
    → ¬ Check b₁
    → IsMove m b b₁
    
  mvBishop : ∀{b₁ sq m whichb sq₁}
    → (B whichb sq) ≡ m
    → (b : BoardArrangement)
    → ¬ Check b
    → OccupiedWith b (bishop whichb) sq
    → (p : T (isDiagonal sq sq₁))
    → NotOccupied b (enumDiagonal sq sq₁ p)
    → ¬ Occupied b sq₁
    → b₁ ≡ mvPiece b (bishop whichb) sq₁
    → ¬ Check b₁
    → IsMove m b b₁

  capBishop : ∀{b₁ sq m whichb sq₁}
    → (Bx whichb sq) ≡ m
    → (b : BoardArrangement)
    → ¬ Check b
    → OccupiedWith b (bishop whichb) sq
    → (p : T (isDiagonal sq sq₁))
    → NotOccupied b (enumDiagonal sq sq₁ p)
    → OccupiedByOpponent b sq₁
    → b₁ ≡ capturePiece b (bishop whichb) sq₁
    → ¬ Check b₁
    → IsMove m b b₁

  mvKnight : ∀{b₁ sq sq₁ m whichk}
    → (N whichk sq₁) ≡ m
    → (b : BoardArrangement)
    → ¬ Check b
    → OccupiedWith b (knight whichk) sq
    → T (isHorseyMove sq sq₁)
    → ¬ Occupied b sq₁
    → b₁ ≡ mvPiece b (knight whichk) sq₁
    → ¬ Check b₁
    → IsMove m b b₁

  capKnight : ∀{b₁ sq m sq₁ whichk}
    → (Nx whichk sq₁) ≡ m
    → (b : BoardArrangement)
    → ¬ Check b
    → OccupiedWith b (knight whichk) sq
    → T (isHorseyMove sq sq₁)
    → OccupiedByOpponent b sq₁
    → b₁ ≡ capturePiece b (knight whichk) sq₁
    → ¬ Check b₁
    → IsMove m b b₁

  mvRook : ∀{b₁ sq m sq₁ whichr}
    → (R whichr sq₁) ≡ m
    → (b : BoardArrangement)
    → ¬ Check b
    → OccupiedWith b (rook whichr) sq
    → (p : T (isStraight sq sq₁))
    → NotOccupied b (enumStraight sq sq₁ p) 
    → ¬ Occupied b sq₁
    → b₁ ≡ markRookMoved whichr (mvPiece b (rook whichr) sq₁)
    → ¬ Check b₁
    → IsMove m b b₁

  capRook : ∀{b₁ sq m sq₁ whichr}
    → (Rx whichr sq₁) ≡ m
    → (b : BoardArrangement)
    → ¬ Check b
    → OccupiedWith b (rook whichr) sq
    → (p : T (isStraight sq sq₁))
    → NotOccupied b (enumStraight sq sq₁ p) 
    → OccupiedByOpponent b sq₁
    → b₁ ≡ markRookMoved whichr (mvPiece b (rook whichr) sq₁)
    → ¬ Check b₁
    → IsMove m b b₁

  mvPawn : ∀{b₁ sq m sq₁ whichp}
    → (P whichp sq₁) ≡ m
    → (b : BoardArrangement)
    → ¬ Check b
    → OccupiedWith b (pawn whichp) sq
    → NotPromoted b whichp
    → T (oneSquareForward b sq₁ sq)
    → ¬ Occupied b sq₁
    → b₁ ≡ movePawn b whichp sq₁
    → ¬ Check b₁
    → IsMove m b₁ b

  capPawn : ∀{b₁ sq m sq₁ whichp}
    → (Px whichp sq₁) ≡ m
    → (b : BoardArrangement)
    → ¬ Check b
    → OccupiedWith b (pawn whichp) sq
    → NotPromoted b whichp
    → T (isCaptureMove b sq sq₁)
    → OccupiedByOpponent b sq₁
    → b₁ ≡ capturePawn b whichp sq₁
    → ¬ Check b₁
    → IsMove m b b₁

  enPassant : ∀{b₁ sq m sq₁ sq₂ whichp}
    → (ep whichp sq₁) ≡ m
    → (b : BoardArrangement)
    → ¬ Check b
    → ¬ T (pawnMoved b whichp)
    → OccupiedWith b (pawn whichp) sq
    → IsEnPassantMove b sq sq₁ sq₂
    → b₁ ≡ doEnPassant b whichp sq₁ sq₂
    → ¬ Check b₁
    → IsMove m b b₁

  promote : ∀{b₁ sq whichp p m}
    → (p= whichp p) ≡ m
    → (b : BoardArrangement)
    → ¬ Check b
    → OccupiedWith b (pawn whichp) sq
    → NotPromoted b whichp
    → T (atTopOrBottom sq)
    → b₁ ≡ promotePawn b whichp p
    → IsMove m b b₁

  mvPromotedKnight : ∀{b₁ sq whichk whichp m sq₁}
    → (P whichp sq₁) ≡ m
    → (b : BoardArrangement)
    → ¬ Check b
    → OccupiedWith b (pawn whichp) sq
    → Promoted b whichp (knight whichk)
    → T (isHorseyMove sq sq₁)
    → ¬ Occupied b sq₁
    → b₁ ≡ mvPiece b (pawn whichp) sq₁
    → ¬ Check b₁
    → IsMove m b b₁

  capPromotedKnight : ∀{b₁ sq whichk whichp m sq₁}
    → (Px whichp sq₁) ≡ m
    → (b : BoardArrangement)
    → ¬ Check b
    → OccupiedWith b (pawn whichp) sq
    → Promoted b whichp (knight whichk)
    → T (isHorseyMove sq sq₁)
    → OccupiedByOpponent b sq₁
    → b₁ ≡ capturePiece b (pawn whichp) sq₁
    → ¬ Check b₁
    → IsMove m b b₁

  mvPromotedQueenStraight : ∀{b₁ sq whichp m sq₁}
    → (P whichp sq₁) ≡ m
    → (b : BoardArrangement)
    → ¬ Check b
    → OccupiedWith b queen sq
    → Promoted b whichp queen
    → (p : T (isStraight sq sq₁))
    → NotOccupied b (enumStraight sq sq₁ p)
    → ¬ Occupied b sq₁
    → b₁ ≡ mvPiece b (pawn whichp) sq₁
    → ¬ Check b₁
    → IsMove m b b₁

  capPromotedQueenStraight : ∀{b₁ sq m whichp sq₁}
    → (Px whichp sq₁) ≡ m
    → (b : BoardArrangement)
    → ¬ Check b
    → OccupiedWith b (pawn whichp) sq
    → Promoted b whichp queen
    → (p : T (isStraight sq sq₁))
    → NotOccupied b (enumStraight sq sq₁ p)
    → OccupiedByOpponent b sq₁
    → b₁ ≡ capturePiece b (pawn whichp) sq₁
    → ¬ Check b₁
    → IsMove m b b₁

  mvPromotedQueenDiagonal : ∀{b₁ sq m whichp sq₁}
    → (P whichp sq₁) ≡ m
    → (b : BoardArrangement)
    → ¬ Check b
    → OccupiedWith b (pawn whichp) sq
    → Promoted b whichp queen
    → (p : T (isDiagonal sq sq₁))
    → NotOccupied b (enumDiagonal sq sq₁ p)
    → ¬ Occupied b sq₁
    → b₁ ≡ mvPiece b (pawn whichp) sq₁
    → ¬ Check b₁
    → IsMove m b b₁

  capPromotedQueenDiagonal : ∀{b₁ sq whichp m sq₁}
    → (Px whichp sq₁) ≡ m
    → (b : BoardArrangement)
    → ¬ Check b
    → OccupiedWith b (pawn whichp) sq
    → Promoted b whichp queen
    → (p : T (isDiagonal sq sq₁))
    → NotOccupied b (enumDiagonal sq sq₁ p)
    → OccupiedByOpponent b sq₁
    → b₁ ≡ capturePiece b (pawn whichp) sq₁
    → ¬ Check b₁
    → IsMove m b b₁

  -- i don't feel like adding rules for every possible promotion
  -- the queen and knight should give you all the flexibility you
  -- need

data Game : List Move → BoardArrangement → Set where
  gameEnd : ∀{b} → Game [] b
  game : ∀{m ms b b₁} → IsMove m b₁ b → Game ms b₁ → Game (m ∷ ms) b

initialBoard : BoardArrangement
initialBoard =
  let s = record {
        kMoved = false
       ; qrMoved = false
       ; krMoved = false
       ; pawnHasMoved = (p1 , false)
                     ∷ (p2 , false)
                     ∷ (p3 , false)
                     ∷ (p4 , false)
                     ∷ (p5 , false)
                     ∷ (p6 , false)
                     ∷ (p7 , false)
                     ∷ (p8 , false)
                     ∷ []
       ; pawnPromotes = (p1 , nothing)
                     ∷ (p2 , nothing)
                     ∷ (p3 , nothing)
                     ∷ (p4 , nothing)
                     ∷ (p5 , nothing)
                     ∷ (p6 , nothing)
                     ∷ (p7 , nothing)
                     ∷ (p8 , nothing)
                     ∷ []
       ; pieces = []
        }
      ws = record s { pieces =
               (rook q   , just (A , #1))
             ∷ (knight q , just (B , #1))
             ∷ (bishop q , just (C , #1))
             ∷ (queen         , just (D , #1))
             ∷ (king          , just (E , #1))
             ∷ (bishop k  , just (F , #1))
             ∷ (knight k  , just (G , #1))
             ∷ (rook k    , just (H , #1))
             ∷ (pawn p1 , just (A , #2))
             ∷ (pawn p2 , just (B , #2))
             ∷ (pawn p3 , just (C , #2))
             ∷ (pawn p4 , just (D , #2))
             ∷ (pawn p5 , just (E , #2))
             ∷ (pawn p6 , just (F , #2))
             ∷ (pawn p7 , just (G , #2))
             ∷ (pawn p8 , just (H , #2))
             ∷ []
           }

      bs = record s { pieces =
               (rook q   , just (A , #8))
             ∷ (knight q , just (B , #8))
             ∷ (bishop q , just (C , #8))
             ∷ (queen         , just (D , #8))
             ∷ (king          , just (E , #8))
             ∷ (bishop k  , just (F , #8))
             ∷ (knight k  , just (G , #8))
             ∷ (rook k    , just (H , #8))
             ∷ (pawn p1 , just (A , #7))
             ∷ (pawn p2 , just (B , #7))
             ∷ (pawn p3 , just (C , #7))
             ∷ (pawn p4 , just (D , #7))
             ∷ (pawn p5 , just (E , #7))
             ∷ (pawn p6 , just (F , #7))
             ∷ (pawn p7 , just (G , #7))
             ∷ (pawn p8 , just (H , #7))
             ∷ [] }
  in record { whosTurn = white
            ; whiteSide = ws
            ; blackSide = bs
            }

b1 : ∀{whichb} → bishop whichb ≡ bishop whichb
b1 = refl

-- holy cow it takes a lot to see that the initial board is not in check
notCheckInitialBoard : ¬ Check initialBoard
notCheckInitialBoard (check (occWith refl) (canAttackKing (occWithOpponentPiece refl) ()))
notCheckInitialBoard (check (occWith refl) (canAttackQueenStraight (occWithOpponentPiece refl) p x₁)) = p
notCheckInitialBoard (check (occWith refl) (canAttackQueenDiagonal (occWithOpponentPiece refl) p x₁)) = p
notCheckInitialBoard (check (occWith refl) (canAttackBishop {k} (occWithOpponentPiece refl) p x₁)) = p
notCheckInitialBoard (check (occWith refl) (canAttackBishop {q} (occWithOpponentPiece refl) p x₁)) = p
notCheckInitialBoard (check (occWith refl) (canAttackKnight {k} (occWithOpponentPiece refl) ()))
notCheckInitialBoard (check (occWith refl) (canAttackKnight {q} (occWithOpponentPiece refl) x₁)) = x₁
notCheckInitialBoard (check (occWith refl) (canAttackRook {k} (occWithOpponentPiece refl) p (notOccStep x x₁))) = p
notCheckInitialBoard (check (occWith refl) (canAttackRook {q} (occWithOpponentPiece refl) p x₁)) = p
notCheckInitialBoard (check (occWith refl) (canAttackPawn {p1} (occWithOpponentPiece refl) x₁)) = x₁
notCheckInitialBoard (check (occWith refl) (canAttackPawn {p2} (occWithOpponentPiece refl) x₁)) = x₁
notCheckInitialBoard (check (occWith refl) (canAttackPawn {p3} (occWithOpponentPiece refl) x₁)) = x₁
notCheckInitialBoard (check (occWith refl) (canAttackPawn {p4} (occWithOpponentPiece refl) x₁)) = x₁
notCheckInitialBoard (check (occWith refl) (canAttackPawn {p5} (occWithOpponentPiece refl) x₁)) = x₁
notCheckInitialBoard (check (occWith refl) (canAttackPawn {p6} (occWithOpponentPiece refl) x₁)) = x₁
notCheckInitialBoard (check (occWith refl) (canAttackPawn {p7} (occWithOpponentPiece refl) x₁)) = x₁
notCheckInitialBoard (check (occWith refl) (canAttackPawn {p8} (occWithOpponentPiece refl) x₁)) = x₁

cb : Game [] initialBoard
cb = gameEnd

-- we have to go through 16*2 pieces
notOccD3 : ¬ Occupied initialBoard (D , #3)
notOccD3 (occupied (next (next (next (next (next (next (next (next (next (next (next (next (next (next (next (next (next (next (next (next (next (next (next (next (next (next (next (next (next (next (next (next ())))))))))))))))))))))))))))))))))

-- same as notCheckInitialBoard
notCheckMoveP4 : ¬ Check (movePawn initialBoard p4 (D , #3))
notCheckMoveP4 (check (occWith refl) (canAttackKing (occWithOpponentPiece refl) ()))
notCheckMoveP4 (check (occWith refl) (canAttackQueenStraight (occWithOpponentPiece refl) p x₁)) = p
notCheckMoveP4 (check (occWith refl) (canAttackQueenDiagonal (occWithOpponentPiece refl) p x₁)) = p
notCheckMoveP4 (check (occWith refl) (canAttackBishop {k} (occWithOpponentPiece refl) p x₁)) = p
notCheckMoveP4 (check (occWith refl) (canAttackBishop {q} (occWithOpponentPiece refl) p x₁)) = p
notCheckMoveP4 (check (occWith refl) (canAttackKnight {k} (occWithOpponentPiece refl) ()))
notCheckMoveP4 (check (occWith refl) (canAttackKnight {q} (occWithOpponentPiece refl) x₁)) = x₁
notCheckMoveP4 (check (occWith refl) (canAttackRook {k} (occWithOpponentPiece refl) p (notOccStep x x₁))) = p
notCheckMoveP4 (check (occWith refl) (canAttackRook {q} (occWithOpponentPiece refl) p x₁)) = p
notCheckMoveP4 (check (occWith refl) (canAttackPawn {p1} (occWithOpponentPiece refl) x₁)) = x₁
notCheckMoveP4 (check (occWith refl) (canAttackPawn {p2} (occWithOpponentPiece refl) x₁)) = x₁
notCheckMoveP4 (check (occWith refl) (canAttackPawn {p3} (occWithOpponentPiece refl) x₁)) = x₁
notCheckMoveP4 (check (occWith refl) (canAttackPawn {p4} (occWithOpponentPiece refl) x₁)) = x₁
notCheckMoveP4 (check (occWith refl) (canAttackPawn {p5} (occWithOpponentPiece refl) x₁)) = x₁
notCheckMoveP4 (check (occWith refl) (canAttackPawn {p6} (occWithOpponentPiece refl) x₁)) = x₁
notCheckMoveP4 (check (occWith refl) (canAttackPawn {p7} (occWithOpponentPiece refl) x₁)) = x₁
notCheckMoveP4 (check (occWith refl) (canAttackPawn {p8} (occWithOpponentPiece refl) x₁)) = x₁

ca : Game (P p4 (D , #3)
          ∷ [])
          initialBoard
ca = game (mvPawn refl initialBoard (notCheckInitialBoard) (occWith refl) (isNotPromotedW refl (Any.there
                                                                                                  (Any.there (Any.there (Any.here (isNotProm refl refl)))))) tt notOccD3 refl notCheckMoveP4) gameEnd
