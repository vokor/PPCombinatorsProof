module BaseFun where

import qualified Prelude
import qualified Data.Bits
import qualified Data.Char

app :: (([]) a1) -> (([]) a1) -> ([]) a1
app l m =
  case l of {
   ([]) -> m;
   (:) a l1 -> (:) a (app l1 m)}

sub :: Prelude.Int -> Prelude.Int -> Prelude.Int
sub = (\n m -> Prelude.max 0 (n Prelude.- m))

compose :: (a2 -> a3) -> (a1 -> a2) -> a1 -> a3
compose g f x =
  g (f x)

flip :: (a1 -> a2 -> a3) -> a2 -> a1 -> a3
flip f x y =
  f y x

data Positive =
   XI Positive
 | XO Positive
 | XH

data N =
   N0
 | Npos Positive

concat :: (([]) (([]) a1)) -> ([]) a1
concat l =
  case l of {
   ([]) -> ([]);
   (:) x l0 -> app x (concat l0)}

map :: (a1 -> a2) -> (([]) a1) -> ([]) a2
map f l =
  case l of {
   ([]) -> ([]);
   (:) a t -> (:) (f a) (map f t)}

fold_left :: (a1 -> a2 -> a1) -> (([]) a2) -> a1 -> a1
fold_left f l a0 =
  case l of {
   ([]) -> a0;
   (:) b t -> fold_left f t (f a0 b)}

fold_right :: (a2 -> a1 -> a1) -> a1 -> (([]) a2) -> a1
fold_right f a0 l =
  case l of {
   ([]) -> a0;
   (:) b t -> f b (fold_right f a0 t)}

existsb :: (a1 -> Prelude.Bool) -> (([]) a1) -> Prelude.Bool
existsb f l =
  case l of {
   ([]) -> Prelude.False;
   (:) a l0 -> (Prelude.||) (f a) (existsb f l0)}

filter :: (a1 -> Prelude.Bool) -> (([]) a1) -> ([]) a1
filter f l =
  case l of {
   ([]) -> ([]);
   (:) x l0 ->
    case f x of {
     Prelude.True -> (:) x (filter f l0);
     Prelude.False -> filter f l0}}

zero :: Prelude.Char
zero =
  '\000'

one :: Prelude.Char
one =
  '\001'

shift :: Prelude.Bool -> Prelude.Char -> Prelude.Char
shift c a =
  (\f a -> f (Data.Bits.testBit (Data.Char.ord a) 0) (Data.Bits.testBit (Data.Char.ord a) 1) (Data.Bits.testBit (Data.Char.ord a) 2) (Data.Bits.testBit (Data.Char.ord a) 3) (Data.Bits.testBit (Data.Char.ord a) 4) (Data.Bits.testBit (Data.Char.ord a) 5) (Data.Bits.testBit (Data.Char.ord a) 6) (Data.Bits.testBit (Data.Char.ord a) 7))
    (\a1 a2 a3 a4 a5 a6 a7 _ ->
    (\b0 b1 b2 b3 b4 b5 b6 b7 -> Data.Char.chr ( (if b0 then Data.Bits.shiftL 1 0 else 0) Prelude.+ (if b1 then Data.Bits.shiftL 1 1 else 0) Prelude.+ (if b2 then Data.Bits.shiftL 1 2 else 0) Prelude.+ (if b3 then Data.Bits.shiftL 1 3 else 0) Prelude.+ (if b4 then Data.Bits.shiftL 1 4 else 0) Prelude.+ (if b5 then Data.Bits.shiftL 1 5 else 0) Prelude.+ (if b6 then Data.Bits.shiftL 1 6 else 0) Prelude.+ (if b7 then Data.Bits.shiftL 1 7 else 0)))
    c a1 a2 a3 a4 a5 a6 a7)
    a

ascii_of_pos :: Positive -> Prelude.Char
ascii_of_pos =
  let {
   loop n p =
     (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
       (\_ -> zero)
       (\n' ->
       case p of {
        XI p' -> shift Prelude.True (loop n' p');
        XO p' -> shift Prelude.False (loop n' p');
        XH -> one})
       n}
  in loop (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
       (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ 0))))))))

ascii_of_N :: N -> Prelude.Char
ascii_of_N n =
  case n of {
   N0 -> zero;
   Npos p -> ascii_of_pos p}

append :: Prelude.String -> Prelude.String -> Prelude.String
append s1 s2 =
  case s1 of {
   ([]) -> s2;
   (:) c s1' -> (:) c (append s1' s2)}

length :: Prelude.String -> Prelude.Int
length s =
  case s of {
   ([]) -> 0;
   (:) _ s' -> Prelude.succ (length s')}

substring :: Prelude.Int -> Prelude.Int -> Prelude.String -> Prelude.String
substring n m s =
  (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
    (\_ ->
    (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
      (\_ -> ([]))
      (\m' -> case s of {
               ([]) -> s;
               (:) c s' -> (:) c (substring 0 m' s')})
      m)
    (\n' -> case s of {
             ([]) -> s;
             (:) _ s' -> substring n' m s'})
    n

prefix :: Prelude.String -> Prelude.String -> Prelude.Bool
prefix s1 s2 =
  case s1 of {
   ([]) -> Prelude.True;
   (:) a s1' ->
    case s2 of {
     ([]) -> Prelude.False;
     (:) b s2' ->
      case (Prelude.==) a b of {
       Prelude.True -> prefix s1' s2';
       Prelude.False -> Prelude.False}}}

index :: Prelude.Int -> Prelude.String -> Prelude.String -> Prelude.Maybe
         Prelude.Int
index n s1 s2 =
  case s2 of {
   ([]) ->
    (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
      (\_ ->
      case s1 of {
       ([]) -> Prelude.Just 0;
       (:) _ _ -> Prelude.Nothing})
      (\_ -> Prelude.Nothing)
      n;
   (:) _ s2' ->
    (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
      (\_ ->
      case prefix s1 s2 of {
       Prelude.True -> Prelude.Just 0;
       Prelude.False ->
        case index 0 s1 s2' of {
         Prelude.Just n0 -> Prelude.Just (Prelude.succ n0);
         Prelude.Nothing -> Prelude.Nothing}})
      (\n' ->
      case index n' s1 s2' of {
       Prelude.Just n0 -> Prelude.Just (Prelude.succ n0);
       Prelude.Nothing -> Prelude.Nothing})
      n}
