module Sessions.Terms.Expr

import Data.SnocList
import Data.SnocList.Elem
import Data.List.Elem

import Extra

import Sessions.Types.Base
import Sessions.Types.Common

public export
data Expr : SnocList Base -> Base -> Type
  where
    True, False : Expr ts BOOL
    N : Nat -> Expr ts NAT
    V : Elem t ts
     -> Expr ts t

    Tag : Elem (s, ty) types
       -> Expr ts ty
       -> Expr ts (SUM types)

-- [ EOF ]
