module Sessions.Types.Global

import public Decidable.Equality

import public Data.SnocList
import public Data.SnocList.Elem

import public Extra

import public Sessions.Types.Base
import public Sessions.Types.Common

{-
public export
data Global : Role.Context
           -> Fix.Context
           -> Type
  where
    Stop : Global rs fs
    Call : {n : _}
        -> AtIndex MkFix fs n
        -> Global rs fs
    Rec : Global rs (fs :< MkFix)
       -> Global rs fs
    Choice : {s,r : _}
          -> (x : AtIndex s rs n)
          -> (y : AtIndex r rs m)
          -> EqualNot x y
          -> List (Branch Global rs fs)
          -> Global rs fs
-}
public export
Global : Role.Context
      -> Fix.Context
      -> Type
Global = Protocol GLOBAL

public export
Branch : Role.Context
      -> Fix.Context
      -> Type
Branch = Branch Global

-- [ EOF ]
