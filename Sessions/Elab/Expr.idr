module Sessions.Elab.Expr

import Data.SnocList
import Data.SnocList.Elem
import Data.List.Elem

import Extra

import Sessions.Types.Base
import Sessions.Types.Common
import Sessions.AST
import Sessions.Terms.Expr

%default total

mutual
  namespace Exprs
    namespace Synth

      public export
      data Expr : SnocList (String,Base) -> Synth.Expr -> Base -> Type where
        True : Expr ts True BOOL
        False : Expr ts False BOOL
        N : (b : Nat) -> Expr ts (N n) NAT
        V : {v : String}
         -> Lookup.Elem (v,b) ts
         -> Expr ts (V v) b

        The : Check.Expr ts ty tm
           -> Expr ts (The ty tm) ty
    namespace Check

      public export
      data Expr : SnocList (String,Base) -> Base -> Check.Expr -> Type
        where
          Switch : Expr ts tm tyA
                -> (prf : tyA = tyB)
                -> Expr ts tyB (Switch tm)

          Tag : {tyE : _}
             -> Synth.Expr ts e tyG
             -> Elem (s,tyE) types
             -> tyE === tyG
             -> Expr ts (SUM types) (Tag s e)

namespace Synth
  export
  unique : (tA : Synth.Expr ctxt term a)
        -> (tB : Synth.Expr ctxt term b)
              -> Equal a b
  unique True True = Refl
  unique False False = Refl
  unique (N x) (N y) = Refl
  unique (V x) (V y) with (Lookup.unique x y)
    unique (V x) (V y) | Refl = Refl
  unique (The x) (The y) = Refl

namespace Expr
  unbound : ((v : Base ** Lookup.Elem (str, v) ts) -> Void) -> DPair Base (Expr ts (V str)) -> Void
  unbound f (fst ** (V x)) = f (fst ** x)

  export
  synth : (ts  : SnocList (String,Base))
       -> (ast : Synth.Expr)
              -> Dec (DPair Base (Expr ts ast))

  switchFails : (tm   : Synth.Expr ts term a)
             -> (no   : Equal a b -> Void)
             -> (this : Check.Expr ts b (Switch term))
                     -> Void
  switchFails tm no (Switch this Refl) with (Synth.unique tm this)
    switchFails tm no (Switch this Refl) | Refl = no Refl


  tagSumNotNat : Expr ts NAT (Tag l e) -> Void
  tagSumNotNat (Switch x prf) impossible
  tagSumNotNat (Tag x y prf) impossible

  tagSumNotBool : Expr ts BOOL (Tag l e) -> Void
  tagSumNotBool (Switch x prf) impossible
  tagSumNotBool (Tag x y prf) impossible


  export
  check : (ts  : SnocList (String,Base))
       -> (ty  : Base)
       -> (ast : Check.Expr)
              -> Dec (Expr ts ty ast)
  check ts ty (Switch x) with (synth ts x)
    check ts ty (Switch x) | (Yes (tyG ** prf)) with (decEq tyG ty)
      check ts ty (Switch x) | (Yes (ty ** prf)) | (Yes Refl)
        = Yes (Switch prf Refl)
      check ts ty (Switch x) | (Yes (tyG ** prf)) | (No no)
        = No (switchFails prf no)

    check ts ty (Switch x) | (No no)
      = No (\case (Switch y Refl) => no (ty ** y))

  check ts NAT (Tag l e)
    = No tagSumNotNat
  check ts BOOL (Tag l e)
    = No tagSumNotBool
  check ts (SUM xs) (Tag l e) with (synth ts e)
    check ts (SUM xs) (Tag l e) | (Yes (tyE ** pTYe)) with (isElem (l, tyE) xs)
      check ts (SUM xs) (Tag l e) | (Yes (tyE ** pTYe)) | (Yes prf)
        = Yes (Tag pTYe prf Refl)
      check ts (SUM xs) (Tag l e) | (Yes (tyE ** pTYe)) | (No contra)
        = No $ \case (Tag x y Refl) => case unique  pTYe x of
                      Refl => contra y

    check ts (SUM xs) (Tag l e) | (No contra)
      = No $ \case (Tag x y Refl) => contra ( _ ** x)

  synth ts True = Yes (BOOL ** True)
  synth ts False = Yes (BOOL ** False)
  synth ts (N k) = Yes (NAT ** N k)
  synth ts (The b tm) with (check ts b tm)
    synth ts (The b tm) | (Yes prf) = Yes (b ** The prf)
    synth ts (The b tm) | (No contra)
      = No (\case (fst ** (The x)) => contra x)

  synth ts (V str) with (lookup ts str)
    synth ts (V str) | (Yes (ty ** idx)) = Yes (ty ** V idx)
    synth ts (V str) | (No no)
        = No (unbound no)


namespace Convert

  namespace Synth
    export
    toTerm : Synth.Expr ctxt e ty
          ->       Expr (erase ctxt) ty

  namespace Check
    export
    toTerm : Check.Expr ctxt ty e
          ->       Expr (erase ctxt) ty


  namespace Synth

    toTerm True = True
    toTerm False = True
    toTerm (N n) = N n
    toTerm (V idx) = V (erase idx)
    toTerm (The x) = Check.toTerm x


  namespace Check
    toTerm (Switch x Refl) = Synth.toTerm x
    toTerm (Tag e idx Refl)
      = Tag idx (toTerm e)




-- [ EOF ]
