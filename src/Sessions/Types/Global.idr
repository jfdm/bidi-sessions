module Sessions.Types.Global

import public Decidable.Equality

import public Data.SnocList
import public Data.SnocList.Elem

import public Extra

import public Sessions.Types.Base
import public Sessions.Types.Common

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
