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
  
sqsAround : Square → List Square
sqsAround (a' , b') =
  let a = fileToℕ a'
      b = rankToℕ b'
      sqs = (a + 1 , b) ∷ (a ∸ 1 , b) ∷ (a , b + 1) ∷ (a , b ∸ 1) ∷ []
  in map (λ{ (c , d) → ℕtoFile c , ℕtoRank d })
         (filter isValid sqs)

-- | is this square relative to that one or that one to this?

data OneFileHigher : Square → Square → Set where
  oneFileHigher : ∀{s q}
    → (file s ∸ file q) ≡ 1
    → OneFileHigher s q
    
data OneFileLower : Square → Square → Set where
  oneFileLower : ∀{s q}
    → (file q ∸ file s) ≡ 1
    → OneFileLower s q
    
data OneRankHigher : Square → Square → Set where
  oneRankHigher : ∀{s q}
    → (rank s ∸ rank q) ≡ 1
    → OneRankHigher s q

data OneRankLower : Square → Square → Set where
  oneRankLower : ∀{s q}
    → (rank q ∸ rank s) ≡ 1
    → OneRankLower s q

data SameFile : Square → Square → Set where
  sameFile : ∀{s q}
    → file s ≡ file q
    → SameFile s q

data SameRank : Square → Square → Set where
  sameRank : ∀{s q}
    → T (rank s > 0 ∧ rank s < 9)
    → rank s ≡ rank q
    → SameRank s q

data North : Square → Square → Set where
  mKNorth : ∀{s q}
    → SameFile s q
    → OneRankHigher s q
    → North s q

data East : Square → Square → Set where
  mkEast : ∀{s q}
    → SameRank s q
    → OneFileHigher s q
    → East s q

data South : Square → Square → Set where
  mkSouth : ∀{s q}
    → SameFile s q
    → OneRankLower s q
    → South s q

data West : Square → Square → Set where
  mkWest : ∀{s q}
    → SameRank s q
    → OneFileLower s q
    → West s q

data NorthEast : Square → Square → Set where
  mkNorthEast : ∀{s q}
    → OneFileHigher s q
    → OneRankHigher s q
    → NorthEast s q

data NorthWest : Square → Square → Set where
  mkNorthWest : ∀{s q}
    → OneRankHigher s q
    → OneFileLower s q
    → NorthWest s q

data SouthEast : Square → Square → Set where
  mkSouthEast : ∀{s q}
    → OneRankLower s q
    → OneFileHigher s q
    → SouthEast s q

data SouthWest : Square → Square → Set where
  mkSouthWest : ∀{s q}
    → OneFileLower s q
    → OneRankLower s q
    → SouthWest s q

-- | Pieces

data Which : Set where
  kings : Which
  queens : Which
 
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
pieceEq (bishop kings)  (bishop kings) = true
pieceEq (bishop queens) (bishop queens) = true
pieceEq (knight kings)  (knight kings) = true
pieceEq (knight queens) (knight queens) = true
pieceEq (rook   kings)  (rook kings) = true
pieceEq (rook   queens) (rook queens) = true
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

turnColor : BoardArrangement → Color
turnColor b = whosTurn b

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
          whiteSide =
            updateSide (whiteSide b) (updatePiece wps p nothing)}
      ; black → record b {
          blackSide =
            updateSide (blackSide b) (updatePiece bps p nothing)}
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
       in mvPiece b' (rook queens) (D , #1)
   ; black → 
       let b' = mvPiece b king (C , #8)
       in mvPiece b' (rook queens) (D , #8)
   }

scastle : BoardArrangement → BoardArrangement
scastle b = 
  case whosTurn b of
  λ{ white →
       let b' = mvPiece b king (G , #1)
       in mvPiece b' (rook kings) (F , #1)
   ; black →
       let b' = mvPiece b king (G , #8)
       in mvPiece b' (rook kings) (F , #8)
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
     λ{ (queens , white) →
           record b {whiteSide = record ws { qrMoved = true }}
      ; (queens , black) →
           record b {blackSide = record bs { qrMoved = true }}
      ; (kings , white) →
           record b {whiteSide = record ws { krMoved = true }}
      ; (kings , black) →
           record b {blackSide = record bs { krMoved = true }}
      }
  
atTopOrBottom : Square → Bool
atTopOrBottom (_ , #1) = true
atTopOrBottom (_ , #8) = true
atTopOrBottom _ = false

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

-- | is a square relative to another or is that one relative to this one?
    
data OneSquareForward : Color → Square → Square → Set where
  isOneSquareForwardW : ∀{c s q}
    → c ≡ white
    → North s q
    → OneSquareForward c s q

  isOneSquareForwardB : ∀{c s q}
    → c ≡ black
    → South s q
    → OneSquareForward c s q

data IsCaptureMove : Color → Square → Square → Set where
  isCaptureMoveWNE : ∀{c s q}
    → c ≡ white
    → NorthEast s q
    → IsCaptureMove c s q

  isCaptureMoveWNW : ∀{c s q}
    → c ≡ white
    → NorthWest s q
    → IsCaptureMove c s q

  isCaptureMoveBSE : ∀{c s q}
    → c ≡ black
    → SouthEast s q
    → IsCaptureMove c s q

  isCaptureMoveBSW : ∀{c s q}
    → c ≡ black
    → SouthWest s q
    → IsCaptureMove c s q

data IsHorseyMove : Square → Square → Set where
  isHorsey1 : ∀{s q t}
    → OneRankLower t s
    → SouthWest q t
    → IsHorseyMove s q

  isHorsey2 : ∀{s q t}
    → OneRankLower t s
    → SouthEast q t
    → IsHorseyMove s q

  isHorsey3 : ∀{s q t}
    → OneRankHigher t s
    → NorthWest q t
    → IsHorseyMove s q

  isHorsey4 : ∀{s q t}
    → OneRankHigher t s
    → NorthEast q t
    → IsHorseyMove s q

  isHorsey5 : ∀{s q t}
    → OneFileLower t s
    → SouthWest q t
    → IsHorseyMove s q

  isHorsey6 : ∀{s q t}
    → OneFileLower t s
    → NorthWest q t
    → IsHorseyMove s q

  isHorsey7 : ∀{s q t}
    → OneFileHigher t s
    → NorthEast q t
    → IsHorseyMove s q

  isHorsey8 : ∀{s q t}
    → OneFileHigher t s
    → SouthEast q t
    → IsHorseyMove s q

-- | the occupation of little bits of land

data Occupied : BoardArrangement → Square → Set where
  occupied : ∀{sq b}
    → (just sq) ∈ sqsOfAllPieces b → Occupied b sq

data OccupiedWith : BoardArrangement → Piece → Square → Set where
  occWith : ∀{b p sq}
    → just sq ≡ sqOfPiece b p
    → OccupiedWith b p sq

data OccupiedByOpponent : BoardArrangement → Square → Set where
  occOpponent : ∀{b sq}
    → just sq ∈ sqsOfOpponentPieces b
    → OccupiedByOpponent b sq

data OccupiedByFriendly : BoardArrangement → Square → Set where
  occFriendly : ∀{b sq}
    → just sq ∈ sqsOfFriendlyPieces b
    → OccupiedByFriendly b sq
    
data NotOccupied : BoardArrangement → Square → Set where
  notOccupied : ∀{b sq}
     → ¬ (just sq) ∈ sqsOfAllPieces b
     → NotOccupied b sq

data DiagonalDir : Set where
  ne : DiagonalDir
  nw : DiagonalDir
  se : DiagonalDir
  sw : DiagonalDir

-- be easier to just make a predicate but here goes
-- we want to enumerate the squares *between* two squares
data NotOccupiedDiagonal : DiagonalDir → BoardArrangement → Square → Square → Set where
  notOccDiagonalNE : ∀{b sq sq₁}
    → NorthEast sq sq₁
    → NotOccupied b sq
    → NotOccupiedDiagonal ne b sq sq₁

  notOccDiagonalNW : ∀{b sq sq₁}
    → NorthWest sq sq₁
    → NotOccupied b sq
    → NotOccupiedDiagonal nw b sq sq₁

  notOccDiagonalSE : ∀{b sq sq₁}
    → SouthEast sq sq₁
    → NotOccupied b sq
    → NotOccupiedDiagonal se b sq sq₁

  notOccDiagonalSW : ∀{b sq sq₁}
    → SouthWest sq sq₁
    → NotOccupied b sq
    → NotOccupiedDiagonal sw b sq sq₁

  continuesDiagonalNE : ∀{b sq sq₁ sq₂}
    → NotOccupiedDiagonal ne b sq sq₁
    → NorthEast sq₂ sq
    → NotOccupied b sq₂
    → NotOccupiedDiagonal ne b sq₂ sq₁

  continuesDiagonalNW : ∀{b sq sq₁ sq₂}
    → NotOccupiedDiagonal nw b sq sq₁
    → NorthWest sq₂ sq
    → NotOccupied b sq₁
    → NotOccupiedDiagonal nw b sq₂ sq₁

  continuesDiagonalSE : ∀{b sq sq₁ sq₂}
    → NotOccupiedDiagonal se b sq sq₁
    → SouthEast sq₂ sq
    → NotOccupied b sq₂
    → NotOccupiedDiagonal se b sq₂ sq₁

  continuesDiagonalSW : ∀{b sq sq₁ sq₂}
    → NotOccupiedDiagonal sw b sq sq₁
    → SouthWest sq₂ sq
    → NotOccupied b sq₂
    → NotOccupiedDiagonal sw b sq₂ sq₁

data StraightDir : Set where
  north : StraightDir
  east : StraightDir
  south : StraightDir
  west : StraightDir

-- as before i don't know that there is an advantage to doing this over
-- using a predicate. as before we are trying to get the squares *between*
-- two squares
data NotOccupiedStraight : StraightDir → BoardArrangement → Square → Square → Set where
  notOccupiedN : ∀{b sq sq₁}
    → SameFile sq sq₁
    → OneRankHigher sq sq₁
    → NotOccupied b sq
    → NotOccupiedStraight north b sq sq₁

  notOccupiedE : ∀{b sq sq₁}
    → SameRank sq sq₁
    → OneFileHigher sq sq₁
    → NotOccupied b sq
    → NotOccupiedStraight east b sq sq₁

  notOccupiedS : ∀{b sq sq₁}
    → SameFile sq sq₁
    → OneRankLower sq sq₁
    → NotOccupied b sq
    → NotOccupiedStraight south b sq sq₁

  notOccupiedW : ∀{b sq sq₁}
    → SameRank sq sq₁
    → OneFileLower sq sq₁
    → NotOccupied b sq
    → NotOccupiedStraight west b sq sq₁

  continuesStraightN : ∀{b sq sq₁ sq₂}
    → NotOccupiedStraight north b sq sq₁
    → SameFile sq₂ sq
    → OneRankHigher sq₂ sq
    → NotOccupied b sq₂
    → NotOccupiedStraight north b sq₂ sq₁

  continuesStraightW : ∀{b sq sq₁ sq₂}
    → NotOccupiedStraight west b sq sq₁
    → SameRank sq₂ sq
    → OneFileLower sq₂ sq
    → NotOccupied b sq₂
    → NotOccupiedStraight west b sq₂ sq₁

  continuesStraightS : ∀{b sq sq₁ sq₂}
    → NotOccupiedStraight south b sq sq₁
    → SameFile sq₂ sq
    → OneRankLower sq₂ sq
    → NotOccupied b sq₂
    → NotOccupiedStraight south b sq₂ sq₁

  continuesStraightE : ∀{b sq sq₁ sq₂} 
    → NotOccupiedStraight east b sq sq₁
    → SameRank sq₂ sq
    → OneFileHigher sq₂ sq
    → NotOccupied b sq₂
    → NotOccupiedStraight east b sq₂ sq₁

data NotOccupiedSCastle : BoardArrangement → Set where
  notOccSCastleW : ∀{b}
    → (whosTurn b ≡ white)
    → NotOccupied b (G , #1)
    → NotOccupied b (F , #1)
    → NotOccupiedSCastle b

  notOccSCastleB : ∀{b}
    → (whosTurn b ≡ black)
    → NotOccupied b (G , #8)
    → NotOccupied b (F , #8)
    → NotOccupiedSCastle b

data NotOccupiedLCastle : BoardArrangement → Set where
  notOccLCastleW : ∀{b}
    → (whosTurn b ≡ white)
    → NotOccupied b (B , #1)
    → NotOccupied b (C , #1)
    → NotOccupied b (D , #1)
    → NotOccupiedLCastle b

  notOccLCastleB : ∀{b}
    → (whosTurn b ≡ black)
    → NotOccupied b (B , #8)
    → NotOccupied b (C , #8)
    → NotOccupied b (D , #8)
    → NotOccupiedLCastle b

data OneSquareAway : Square → Square → Set where
  oneSquareAwayN : ∀{s q} → North s q → OneSquareAway s q
  oneSquareAwayE : ∀{s q} → East s q  → OneSquareAway s q
  oneSquareAwayS : ∀{s q} → South s q → OneSquareAway s q
  oneSquareAwayW : ∀{s q} → West s q → OneSquareAway s q
  oneSquareAwayNE : ∀{s q} → NorthEast s q  → OneSquareAway s q
  oneSquareAwayNW : ∀{s q} → NorthWest s q → OneSquareAway s q
  oneSquareAwaySE : ∀{s q} → SouthEast s q → OneSquareAway s q
  oneSquareAwaySW : ∀{s q} → SouthWest s q → OneSquareAway s q
   
-- | kings and their being in check

data CanBeAttacked : BoardArrangement → Square → Set where
  canAttackKing : ∀{b sq ksq}
    → OccupiedWith b king ksq
    → OneSquareAway sq ksq
    → CanBeAttacked b sq

  canAttackQueenStraight : ∀{b d sq qsq}
    → OccupiedWith b queen qsq
    → NotOccupiedStraight d b sq qsq
    → CanBeAttacked b sq
    
  canAttackQueenDiagonal : ∀{b d sq qsq}
    → OccupiedWith b queen qsq
    → NotOccupiedStraight d b sq qsq
    → CanBeAttacked b sq

  canAttackBishop : ∀{b d sq bsq whichb}
    → OccupiedWith b (bishop whichb) bsq
    → NotOccupiedDiagonal d b sq bsq
    → CanBeAttacked b sq

  canAttackKnight : ∀{b sq ksq whichk}
    → OccupiedWith b (knight whichk) ksq
    → IsHorseyMove sq ksq
    → CanBeAttacked b sq

  canAttackRook : ∀{b d sq rsq whichr}
    → OccupiedWith b (rook whichr) rsq
    → NotOccupiedStraight d b sq rsq
    → CanBeAttacked b sq

  canAttackPawn : ∀{b sq psq whichp}
    → OccupiedWith b (pawn whichp) psq
    → IsCaptureMove (turnColor b) sq psq
    → CanBeAttacked b sq

data Check : BoardArrangement → Set where
  check : ∀{b sq}
    → {_ : OccupiedWith b king sq}
    → {_ : CanBeAttacked b sq}
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

-- | The Moves

-- i'd like to have capture and movement in the same rule but i don't
-- know how to do it so specifying them separately will do

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

data Move : BoardArrangement → Set where
  mvKing : ∀{b₁ sq}
    → (sq₁ : Square)
    → (b : BoardArrangement)
    → {_ : ¬ Checkmate b}
    → {_ : OccupiedWith b king sq}
    → {_ : OneSquareAway sq sq₁}
    → {_ : NotOccupied b sq₁}
    → {_ : b₁ ≡ markKingMoved (mvPiece b king sq₁)}
    → {_ : ¬ Check b₁}
    → Move b₁

  capKing : ∀{b₁ sq}
    → (sq₁ : Square)
    → (b : BoardArrangement)
    → {_ : ¬ Checkmate b}
    → {_ : OccupiedWith b king sq}
    → {_ : OneSquareAway sq sq₁}
    → {_ : OccupiedByOpponent b sq₁}
    → {_ : b₁ ≡ capturePiece b king sq₁}
    → {_ : ¬ Check b₁}
    → Move b₁

  longCastle : ∀{b₁}
    → (b : BoardArrangement)
    → {_ : ¬ Checkmate b}
    → {_ : ¬ T (kMoved (turnSide b))}
    → {_ : ¬ T (qrMoved (turnSide b))}
    → {_ : ¬ (CanBeAttacked b (lcastlePassesThroughSquare b))}
    → {_ : NotOccupiedLCastle b }
    → {_ : b₁ ≡ lcastle b}
    → {_ : ¬ Check b₁}
    → Move b₁

  shortCastle : ∀{b₁}
    → (b : BoardArrangement)
    → {_ : ¬ Checkmate b}
    → {_ : ¬ T (kMoved (turnSide b))}
    → {_ : ¬ T (krMoved (turnSide b))}
    → {_ : ¬ CanBeAttacked b (scastlePassesThroughSquare b)}
    → {_ : NotOccupiedSCastle b}
    → {_ : b₁ ≡ scastle b}
    → {_ : ¬ Check b₁}
    → Move b₁
    
  mvQueenStraight : ∀{b₁ d sq}
    → (sq₁ : Square)
    → (b : BoardArrangement)
    → {_ : ¬ Check b}
    → {_ : OccupiedWith b queen sq}
    → {_ : NotOccupiedStraight d b sq sq₁}
    → {_ : NotOccupied b sq₁}
    → {_ : b₁ ≡ mvPiece b queen sq₁}
    → {_ : ¬ Check b₁}
    → Move b₁

  capQueenStraight : ∀{b₁ d sq}
    → (sq₁ : Square)
    → (b : BoardArrangement)
    → {_ : ¬ Check b}
    → {_ : OccupiedWith b queen sq}
    → {_ : NotOccupiedStraight d b sq sq₁}
    → {_ : OccupiedByOpponent b sq₁}
    → {_ : b₁ ≡ capturePiece b queen sq₁}
    → {_ : ¬ Check b₁}
    → Move b₁

  mvQueenDiagonal : ∀{b₁ d sq}
    → (sq₁ : Square)
    → (b : BoardArrangement)
    → {_ : ¬ Check b}
    → {_ : OccupiedWith b queen sq}
    → {_ : NotOccupiedDiagonal d b sq sq₁}
    → {_ : NotOccupied b sq₁}
    → {_ : b₁ ≡ mvPiece b queen sq₁}
    → {_ : ¬ Check b₁}
    → Move b₁

  capQueenDiagonal : ∀{b₁ d sq}
    → (sq₁ : Square)
    → (b : BoardArrangement)
    → {_ : ¬ Check b}
    → {_ : OccupiedWith b queen sq}
    → {_ : NotOccupiedDiagonal d b sq sq₁}
    → {_ : OccupiedByOpponent b sq₁}
    → {_ : b₁ ≡ capturePiece b queen sq₁}
    → {_ : ¬ Check b₁}
    → Move b₁
    
  mvBishop : ∀{b₁ d sq}
    → (whichb : Which)
    → (sq₁ : Square)
    → (b : BoardArrangement)
    → {_ : ¬ Check b}
    → {_ : OccupiedWith b (bishop whichb) sq}
    → {_ : NotOccupiedDiagonal d b sq sq₁}
    → {_ : NotOccupied b sq₁}
    → {_ : b₁ ≡ mvPiece b (bishop whichb) sq₁}
    → {_ : ¬ Check b₁}
    → Move b₁

  capBishop : ∀{b₁ d sq}
    → (whichb : Which)
    → (sq₁ : Square)
    → (b : BoardArrangement)
    → {_ : ¬ Check b}
    → {_ : OccupiedWith b (bishop whichb) sq}
    → {_ : NotOccupiedDiagonal d b sq sq₁}
    → {_ : OccupiedByOpponent b sq₁}
    → {_ : b₁ ≡ capturePiece b (bishop whichb) sq₁}
    → {_ : ¬ Check b₁}
    → Move b₁

  mvKnight : ∀{b₁ sq}
    → (whichk : Which)
    → (sq₁ : Square)
    → (b : BoardArrangement)
    → {_ : ¬ Check b}
    → {_ : OccupiedWith b (knight whichk) sq}
    → {_ : IsHorseyMove sq sq₁}
    → {_ : NotOccupied b sq₁}
    → {_ : b₁ ≡ mvPiece b (knight whichk) sq₁}
    → {_ : ¬ Check b₁}
    → Move b₁

  capKnight : ∀{b₁ sq}
    → (whichk : Which)
    → (sq₁ : Square)
    → (b : BoardArrangement)
    → {_ : ¬ Check b}
    → {_ : OccupiedWith b (knight whichk) sq}
    → {_ : IsHorseyMove sq sq₁}
    → {_ : OccupiedByOpponent b sq₁}
    → {_ : b₁ ≡ capturePiece b (knight whichk) sq₁}
    → {_ : ¬ Check b₁}
    → Move b₁

  mvRook : ∀{b₁ d sq}
    → (whichr : Which)
    → (sq₁ : Square)
    → (b : BoardArrangement)
    → {_ : ¬ Check b}
    → {_ : OccupiedWith b (rook whichr) sq}
    → {_ : NotOccupiedStraight d b sq sq₁}
    → {_ : NotOccupied b sq₁}
    → {_ : b₁ ≡ markRookMoved whichr (mvPiece b (rook whichr) sq₁)}
    → {_ : ¬ Check b₁}
    → Move b₁

  capRook : ∀{b₁ d sq}
    → (whichr : Which)
    → (sq₁ : Square)
    → (b : BoardArrangement)
    → {_ : ¬ Check b}
    → {_ : OccupiedWith b (rook whichr) sq}
    → {_ : NotOccupiedStraight d b sq sq₁}
    → {_ : OccupiedByOpponent b sq₁}
    → {_ : b₁ ≡ markRookMoved whichr (mvPiece b (rook whichr) sq₁)}
    → {_ : ¬ Check b₁}
    → Move b₁

  mvPawn : ∀{b₁ sq}
    → (whichp : WhichPawn)
    → (sq₁ : Square)
    → (b : BoardArrangement)
    → {_ : ¬ Check b}
    → {_ : OccupiedWith b (pawn whichp) sq}
    → {_ : NotPromoted b whichp}
    → {_ : OneSquareForward (turnColor b) sq sq₁}
    → {_ : NotOccupied b sq₁}
    → {_ : b₁ ≡ mvPiece b (pawn whichp) sq₁}
    → {_ : ¬ Check b₁}
    → Move b₁

  capPawn : ∀{b₁ sq}
    → (whichp : WhichPawn)
    → (sq₁ : Square)
    → (b : BoardArrangement)
    → {_ : ¬ Check b}
    → {_ : OccupiedWith b (pawn whichp) sq}
    → {_ : NotPromoted b whichp}
    → {_ : IsCaptureMove (turnColor b) sq sq₁}
    → {_ : OccupiedByOpponent b sq₁}
    → {_ : b₁ ≡ capturePiece b (pawn whichp) sq₁}
    → {_ : ¬ Check b₁}
    → Move b₁

  promote : ∀{b₁ sq}
    → (whichp : WhichPawn)
    → (p : Piece)
    → (b : BoardArrangement)
    → {_ : ¬ Check b}
    → {_ : OccupiedWith b (pawn whichp) sq}
    → {_ : NotPromoted b whichp}
    → {_ : T (atTopOrBottom sq)}
    → {_ : b₁ ≡ promotePawn b whichp p}
    → Move b₁

  mvPromotedKnight : ∀{b₁ sq whichk}
    → (whichp : WhichPawn)
    → (sq₁ : Square)
    → (b : BoardArrangement)
    → {_ : ¬ Check b}
    → {_ : OccupiedWith b (pawn whichp) sq}
    → {_ : Promoted b whichp (knight whichk)}
    → {_ : IsHorseyMove sq sq₁}
    → {_ : NotOccupied b sq₁}
    → {_ : b₁ ≡ mvPiece b (pawn whichp) sq₁}
    → {_ : ¬ Check b₁}
    → Move b₁

  capPromotedKnight : ∀{b₁ sq whichk}
    → (whichp : WhichPawn)
    → (sq₁ : Square)
    → (b : BoardArrangement)
    → {_ : ¬ Check b}
    → {_ : OccupiedWith b (pawn whichp) sq}
    → {_ : Promoted b whichp (knight whichk)}
    → {_ : IsHorseyMove sq sq₁}
    → {_ : OccupiedByOpponent b sq₁}
    → {_ : b₁ ≡ capturePiece b (pawn whichp) sq₁}
    → {_ : ¬ Check b₁}
    → Move b₁

  mvPromotedQueenStraight : ∀{b₁ d sq}
    → (whichp : WhichPawn)
    → (sq₁ : Square)
    → (b : BoardArrangement)
    → {_ : ¬ Check b}
    → {_ : OccupiedWith b queen sq}
    → {_ : Promoted b whichp queen}
    → {_ : NotOccupiedStraight d b sq sq₁}
    → {_ : NotOccupied b sq₁}
    → {_ : b₁ ≡ mvPiece b (pawn whichp) sq₁}
    → {_ : ¬ Check b₁}
    → Move b₁

  capPromotedQueenStraight : ∀{b₁ d sq}
    → (whichp : WhichPawn)
    → (sq₁ : Square)
    → (b : BoardArrangement)
    → {_ : ¬ Check b}
    → {_ : OccupiedWith b (pawn whichp) sq}
    → {_ : Promoted b whichp queen}
    → {_ : NotOccupiedStraight d b sq sq₁}
    → {_ : OccupiedByOpponent b sq₁}
    → {_ : b₁ ≡ capturePiece b (pawn whichp) sq₁}
    → {_ : ¬ Check b₁}
    → Move b₁

  mvPromotedQueenDiagonal : ∀{b₁ d sq}
    → (whichp : WhichPawn)
    → (sq₁ : Square)
    → (b : BoardArrangement)
    → {_ : ¬ Check b}
    → {_ : OccupiedWith b (pawn whichp) sq}
    → {_ : Promoted b whichp queen}
    → {_ : NotOccupiedDiagonal d b sq sq₁}
    → {_ : NotOccupied b sq₁}
    → {_ : b₁ ≡ mvPiece b (pawn whichp) sq₁}
    → {_ : ¬ Check b₁}
    → Move b₁

  capPromotedQueenDiagonal : ∀{b₁ d sq}
    → (whichp : WhichPawn)
    → (sq₁ : Square)
    → (b : BoardArrangement)
    → {_ : ¬ Check b}
    → {_ : OccupiedWith b (pawn whichp) sq}
    → {_ : Promoted b whichp queen}
    → {_ : NotOccupiedDiagonal d b sq sq₁}
    → {_ : OccupiedByOpponent b sq₁}
    → {_ : b₁ ≡ capturePiece b (pawn whichp) sq₁}
    → {_ : ¬ Check b₁}
    → Move b₁

  -- i don't feel like adding rules for every possible promotion
  -- the queen and knight should give you all the flexibility you
  -- need

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
               (rook queens   , just (A , #1))
             ∷ (knight queens , just (B , #1))
             ∷ (bishop queens , just (C , #1))
             ∷ (queen         , just (D , #1))
             ∷ (king          , just (E , #1))
             ∷ (bishop kings  , just (F , #1))
             ∷ (knight kings  , just (G , #1))
             ∷ (rook kings    , just (H , #1))
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
               (rook queens   , just (A , #8))
             ∷ (knight queens , just (B , #8))
             ∷ (bishop queens , just (C , #8))
             ∷ (queen         , just (D , #8))
             ∷ (king          , just (E , #8))
             ∷ (bishop kings  , just (F , #8))
             ∷ (knight kings  , just (G , #8))
             ∷ (rook kings    , just (H , #8))
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


notCheckInitialBoard : ¬ Check initialBoard
notCheckInitialBoard check = {!!}

aa = mvQueenStraight (D , #3) initialBoard

{-
notCheckInitialBoard : ¬ Check initialBoard
notCheckInitialBoard (check (occWith refl) (canAttackKing (occWith refl) (oneSquareAwayN (mKNorth x x₁)))) = {!!}
notCheckInitialBoard (check (occWith refl) (canAttackKing (occWith refl) (oneSquareAwayE x))) = {!!}
notCheckInitialBoard (check (occWith refl) (canAttackKing (occWith refl) (oneSquareAwayS x))) = {!!}
notCheckInitialBoard (check (occWith refl) (canAttackKing (occWith refl) (oneSquareAwayW x))) = {!!}
notCheckInitialBoard (check (occWith refl) (canAttackKing (occWith refl) (oneSquareAwayNE x))) = {!!}
notCheckInitialBoard (check (occWith refl) (canAttackKing (occWith refl) (oneSquareAwayNW x))) = {!!}
notCheckInitialBoard (check (occWith refl) (canAttackKing (occWith refl) (oneSquareAwaySE x))) = {!!}
notCheckInitialBoard (check (occWith refl) (canAttackKing (occWith refl) (oneSquareAwaySW x))) = {!!}
notCheckInitialBoard (check (occWith refl) (canAttackQueenStraight x x₁)) = {!!}
notCheckInitialBoard (check (occWith refl) (canAttackQueenDiagonal x x₁)) = {!!}
notCheckInitialBoard (check (occWith refl) (canAttackBishop x x₁)) = {!!}
notCheckInitialBoard (check (occWith refl) (canAttackKnight x x₁)) = {!!}
notCheckInitialBoard (check (occWith refl) (canAttackRook x x₁)) = {!!}
notCheckInitialBoard (check (occWith refl) (canAttackPawn x x₁)) = {!!}

-}
