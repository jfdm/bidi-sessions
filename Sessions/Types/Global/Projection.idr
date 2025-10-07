module Sessions.Types.Global.Projection

import Decidable.Equality

import Data.SnocList
import Data.SnocList.Elem

import  Extra

import Sessions.Types.Global
import Sessions.Types.Local
import Sessions.Types.Local.Merge.Projection
import Sessions.Types.Local.Merge.Fold

%default total

namespace Merge

  public export
  data Project : (how : (p : AtIndex r rs n) -> (g : Global rs fs) -> (l : Local rs fs) -> Type)
              -> (p : AtIndex r rs n)
              -> (xs : List (Global.Branch rs fs))
              -> (y  : List (Local rs fs))
                    -> Type

    where
      Last : Project how p Nil Nil
      Next : how p x y
          -> Project how p xs ys
          -> Project how p (B l t x::xs) (y::ys)

namespace Branches

  public export
  data Project : (how : (p : AtIndex r rs n) -> (g : Global rs fs) -> (l : Local rs fs) -> Type)
              -> (p : AtIndex r rs n)
              -> (xs : List (Global.Branch rs fs))
              -> (ys : List (Local.Branch rs fs))
                    -> Type
    where
      Stop : Project how whom Nil Nil
      Next : how whom x y
          -> Branches.Project how whom xs ys
          -> Project how whom (B l t x::xs) (B l t y::ys)

data Project : (p : AtIndex r rs n)
            -> (g : Global rs fs)
            -> (l : Local rs fs)
                 -> Type
  where
    Stop : Project p Stop  Stop
    Call : Project p (Call idx) (Call idx)
    Rec : Project p x y
       -> Project p (Rec x) (Rec y)

    Select : (prf : whom = s)
          -> (bs  : Branches.Project Project whom xs ys)
                 -> Project whom
                            (Choice s r notSR xs)
                            (Comm SEND r ys )

    Offer : (prf : whom = r)
         -> (bs  : Branches.Project Project whom xs ys)
                -> Project whom
                           (Choice s r notSR xs)
                           (Comm RECV s ys)

    Merge : (prfS : EqualNot whom s)
         -> (prfR : EqualNot whom r)
         -> (prfM : Merge.Project Project whom xs ys)
         -> (prfF : Reduce ys y)
                 -> Project whom
                            (Choice s r notSR xs)
                            y

-- [ EOF ]
