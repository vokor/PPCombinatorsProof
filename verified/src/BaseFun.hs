module BaseFun where

import Data.Type.Natural

andb :: Bool -> Bool -> Bool
andb b1 b2 =
  case b1 of {
   True -> b2;
   False -> False}

orb :: Bool -> Bool -> Bool
orb b1 b2 =
  case b1 of {
   True -> True;
   False -> b2}

negb :: Bool -> Bool
negb b =
  case b of {
   True -> False;
   False -> True}

data Option a =
   Some a
 | None

data List a =
   Nil
 | Cons a (List a)

app :: [a1] -> [a1] -> [a1]
app l m =
  case l of {
   [] -> m;
   a:l1 -> a:(app l1 m)}

add :: Nat -> Nat -> Nat
add n m =
  case n of {
   Z -> m;
   S p -> S (add p m)}

sub :: Nat -> Nat -> Nat
sub n m =
  case n of {
   Z -> n;
   S k -> case m of {
           Z -> n;
           S l -> sub k l}}

compose :: (a2 -> a3) -> (a1 -> a2) -> a1 -> a3
compose g f x =
  g (f x)

eqb :: Nat -> Nat -> Bool
eqb n m =
  case n of {
   Z -> case m of {
         Z -> True;
         S _ -> False};
   S n' -> case m of {
            Z -> False;
            S m' -> eqb n' m'}}

leb :: Nat -> Nat -> Bool
leb n m =
  case n of {
   Z -> True;
   S n' -> case m of {
            Z -> False;
            S m' -> leb n' m'}}

existsb :: (a1 -> Bool) -> [a1] -> Bool
existsb f l =
  case l of {
   [] -> False;
   a:l0 -> orb (f a) (existsb f l0)}

append :: String -> String -> String
append s1 s2 = s1 ++ s2

substring :: Nat -> Nat -> String -> String
substring n m s =
  case n of {
   Z ->
    case m of {
     Z -> "";
     S m' ->
      case s of {
       "" -> s;
       c:s' -> c:(substring Z m' s')}};
   S n' -> case s of {
            "" -> s;
            _:s' -> substring n' m s'}}

prefix :: String -> String -> Bool
prefix s1 s2 =
  case s1 of {
   "" -> True;
   a:s1' ->
    case s2 of {
     "" -> False;
     b:s2' -> if a == b then prefix s1' s2'
              else False}}

index :: Nat -> String -> String -> Option Nat
index n s1 s2 =
  case s2 of {
   "" ->
    case n of {
     Z -> case s1 of {
           "" -> Some Z;
           _:_ -> None};
     S _ -> None};
   _:s2' ->
    case n of {
     Z ->
      case prefix s1 s2 of {
       True -> Some Z;
       False ->
        case index Z s1 s2' of {
         Some n0 -> Some (S n0);
         None -> None}};
     S n' -> case index n' s1 s2' of {
              Some n0 -> Some (S n0);
              None -> None}}}
