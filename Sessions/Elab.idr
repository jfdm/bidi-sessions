module Sessions.Elab

import Sessions.Types.Local
import Sessions.Types.Local.Subset
import Sessions.Types.Local.Merge.Synthesis
import Sessions.AST

mutual
  namespace Exprs
    namespace Synth

      public export
      data Expr : SnocList (String,Base) -> Synth.Expr -> Base -> Type where
        True : Expr ts True BOOL
        False : Expr ts False BOOL
        N : Expr ts (N n) NAT
        V : Lookup.Elem (v,b) ts
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

namespace Synth
  export
  unique : (tA : Synth.Expr ctxt term a)
        -> (tB : Synth.Expr ctxt term b)
              -> Equal a b
  unique True True = Refl
  unique False False = Refl
  unique N N = Refl
  unique (V x) (V y) = Lookup.unique x y
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


  synth ts True = Yes (BOOL ** True)
  synth ts False = Yes (BOOL ** False)
  synth ts (N k) = Yes (NAT ** N)
  synth ts (The b tm) with (check ts b tm)
    synth ts (The b (Switch tm)) | (Yes prf) = Yes (b ** The prf)
    synth ts (The b tm) | (No contra)
      = No (\case (fst ** (The x)) => contra x)

  synth ts (V str) with (lookup ts str)
    synth ts (V str) | (Yes (ty ** idx)) = Yes (ty ** V idx)
    synth ts (V str) | (No no)
        = No (unbound no)


namespace Synth
  namespace Local
    namespace Branches
      public export
      data Local : (how : (rs : SnocList Role)
                       -> (fs : SnocList Fix)
                       -> (tm : Local)
                       -> (ty : Local rs fs)
                             -> Type)
                -> (rs  : SnocList Role)
                -> (fs  : SnocList Fix)
                -> (tms : List (String, Base, Local))
                -> (tys : List (Branch rs fs))
                       -> Type
        where
          End : Local how rs fs Nil Nil
          Ext : {0 how : (rs : SnocList Role)
                      -> (fs : SnocList Fix)
                      -> (tm : Local)
                      -> (ty : Local rs fs)
                            -> Type}
             -> (head : how rs fs ktm kty)
             -> (next : Local how rs fs tms tys)
                     -> Local how rs fs ((l,b,ktm)::tms) (B l b kty :: tys)

      export
      synth : {0 how : (rs : SnocList Role)
                    -> (fs : SnocList Fix)
                    -> (tm : Local)
                    -> (ty : Local rs fs)
                          -> Type}
           -> (f : (rs : SnocList Role)
                -> (fs : SnocList Fix)
                -> (tm : Local)
                      -> Dec (DPair (Local rs fs) (how rs fs tm)))
           -> (rs  : SnocList Role)
           -> (fs  : SnocList Fix)
           -> (tms : List (String, Base, Local))
                  -> Dec (DPair (List (Branch rs fs))
                                (Branches.Local how rs fs tms))
      synth f rs fs []
        = Yes ([] ** End)

      synth f rs fs ((l,b,x) :: xs) with (f rs fs x)
        synth f rs fs ((l,b,x) :: xs) | (Yes (ty ** tm)) with (synth f rs fs xs)
          synth f rs fs ((l,b,x) :: xs) | (Yes (ty ** tm)) | (Yes (tys ** tms))
            = Yes (B l b ty :: tys ** Ext tm tms)
          synth f rs fs ((l,b,x) :: xs) | (Yes (ty ** tm)) | (No no)
            = No (\case ((B l b kty :: tys) ** (Ext head next)) => no (tys ** next))

        synth f rs fs ((l,b,x) :: xs) | (No noH)
          = No (\case ((B l b kty :: tys) ** (Ext head next)) => noH (kty ** head))

    public export
    data Local : (rs : SnocList Role)
              -> (fs : SnocList Fix)
              -> (tm : Local)
              -> (ty : Local rs fs)
                    -> Type
      where
        End : Local rs fs End Stop
        Call : (idx : Elem (MkFix f) fs)
                   -> Local rs fs (Call f) (Call idx)
        Rec : Local rs (fs :< MkFix f) kast kty
           -> Local rs fs (Rec f kast) (Rec (MkFix f) kty)

        Comm : (idx : Elem (MkRole r) rs)
            -> Local Local rs fs tms tys
            -> Local rs fs (Comm cty r tms) (Comm cty idx tys)

    export
    synth : (rs : SnocList Role)
         -> (fs : SnocList Fix)
         -> (tm : Local)
               -> Dec (DPair (Local rs fs)
                             (Local rs fs tm))
    synth rs fs End
      = Yes (Stop ** End)

    synth rs fs (Call str) with (isElem (MkFix str) fs)
      synth rs fs (Call str) | (Yes prf)
        = Yes (Call prf ** Call prf)
      synth rs fs (Call str) | (No no)
        = No (\case ((Call idx) ** (Call idx)) => no idx)

    synth rs fs (Rec str k) with (synth rs (fs :< MkFix str) k)
      synth rs fs (Rec str k) | (Yes (kty ** prf))
        = Yes (Rec (MkFix str) kty ** Rec prf)
      synth rs fs (Rec str k) | (No no)
        = No (\case ((Rec (MkFix str) kty) ** (Rec x)) => no (kty ** x))

    synth rs fs (Comm cty r bs) with (isElem (MkRole r) rs)
      synth rs fs (Comm cty r bs) | (Yes ridx) with (synth synth rs fs bs)
        synth rs fs (Comm cty r bs) | (Yes ridx) | (Yes (tys ** tms))
          = Yes (Comm cty ridx tys ** Comm ridx tms)
        synth rs fs (Comm cty r bs) | (Yes ridx) | (No no)
          = No (\case ((Comm cty idx tys) ** (Comm idx x)) => no (tys ** x))

      synth rs fs (Comm cty r bs) | (No no)
        = No (\case (Comm cty idx tys ** Comm idx x) => no idx)

mutual
  namespace Branches
    public export
    data Synth : (rs : SnocList Role)
              -> (fs : SnocList Fix)
              -> (ts : SnocList (String,Base))
              -> (tms : List (String, String, Base, Synth.AST))
              -> (tys : List (Branch rs fs))
                     -> Type
      where
        End : Synth rs fs ts Nil Nil
        Ext : Synth rs fs (ts :< (v, b)) tm ty
           -> Synth rs fs ts tms tys
           -> Synth rs fs ts ((l,v,b,tm)::tms) (B l b ty :: tys)

  public export
  data Synth : (rs : SnocList Role)
            -> (fs : SnocList Fix)
            -> (ts : SnocList (String,Base))
            -> (tm : Synth.AST)
            -> (ty : Local rs fs)
                  -> Type
    where
      Stop : Synth rs fs ts Stop Stop
      Call : (idx : Elem (MkFix f) fs)
                 -> Synth rs fs ts (Call f) (Call idx)
      Loop : (cont : Synth rs (fs :< MkFix f) ts tm  ty)
                  -> Synth rs  fs    ts (Loop f  tm) (Rec (MkFix f) ty)

      Send : (prf  : Elem (MkRole r) rs)
          -> (cont : Synth rs fs ts tm ty)
                  -> Synth rs fs ts (Send r l b tm)
                                 (Comm SEND idx [B l b ty])

      Recv : (idx : Elem (MkRole r) rs)
          -> (bs  : Synth rs fs ts tms tys)
                 -> Synth rs fs ts (Recv r tms) (Comm RECV idx tys)

      If : (l,r : Local rs fs)
        -> (cond : Expr ts BOOL c)
        -> (tt   : Synth rs fs ts ttm l)
        -> (ff   : Synth rs fs ts ffm r)
        -> (prf  : Merge l r ty)
                -> Synth rs fs ts (If c ttm ffm) ty

      The : (ty : Local rs fs)
         -> Local rs fs    tmty ty
         -> Check rs fs ts ty tm
         -> Synth rs fs ts (The tmty tm) ty

  public export
  data Check : (rs : SnocList Role)
            -> (fs : SnocList Fix)
            -> (ts : SnocList (String,Base))
            -> (ty : Local rs fs)
            -> (tm : Check.AST)
                  -> Type
    where
      Switch : (tySyn : Local rs fs)
            -> Synth rs fs ts tm tySyn
            -> Subset tySyn tyCheck
            -> Check rs fs ts tyCheck (Switch tm)

namespace Branches
  export
  synth : (rs : SnocList Role)
       -> (fs : SnocList Fix)
       -> (ts : SnocList (String,Base))
       -> (tms : List (String, String, Base, Synth.AST))
              -> Dec (DPair (List (Branch rs fs))
                            (Synth rs fs ts tms))

export
synth : (rs : SnocList Role)
     -> (fs : SnocList Fix)
     -> (ts : SnocList (String,Base))
     -> (tm : Synth.AST)
           -> Dec (DPair (Local rs fs)
                         (Synth rs fs ts tm))

export
check : (rs : SnocList Role)
     -> (fs : SnocList Fix)
     -> (ts : SnocList (String,Base))
     -> (ty : Local rs fs)
     -> (tm : Check.AST)
           -> Dec (Check rs fs ts ty tm)


namespace Branches
  synth rs fs ts []
    = Yes ([] ** End)
  synth rs fs ts ((l,v,b,k) :: xs) with (synth rs fs (ts :< (v,b)) k)
    synth rs fs ts ((l,v,b,k) :: xs) | (Yes (ty ** tm)) with (synth rs fs ts xs)
      synth rs fs ts ((l,v,b,k) :: xs) | (Yes (ty ** tm)) | (Yes (tys ** tms))
        = Yes (B l b ty :: tys ** Ext tm tms)
      synth rs fs ts ((l,v,b,k) :: xs) | (Yes (ty ** tm)) | (No no)
        = No (\case ((B l b ty :: tys) ** (Ext x y)) => no (tys ** y))

    synth rs fs ts ((l,v,b,k) :: xs) | (No no)
      = No (\case ((B l b ty :: tys) ** (Ext x y)) => no (ty ** x))


checkFails : Local rs fs    type' type
          -> (Check rs fs ts type tm -> Void)
          -> DPair (Local rs fs)
                   (Synth rs fs ts (The type' tm))
          -> Void
checkFails x f (fst ** (The fst y z)) = f ?as -- (rewrite sym (Local.unique x ?a) in z)

synth rs fs ts Stop
  = Yes (Stop ** Stop)

synth rs fs ts (Call str) with (isElem (MkFix str) fs)
  synth rs fs ts (Call str) | (Yes prf)
    = Yes (Call prf ** Call prf)
  synth rs fs ts (Call str) | (No no)
    = No (\case ((Call idx) ** (Call idx)) => no idx)

synth rs fs ts (Loop str k) with (synth rs (fs :< MkFix str) ts k)
  synth rs fs ts (Loop str k) | (Yes (ty ** prf))
    = Yes (Rec (MkFix str) ty ** Loop prf)
  synth rs fs ts (Loop str k) | (No no)
    = No (\case ((Rec (MkFix str) ty) ** (Loop cont)) => no (ty ** cont))

synth rs fs ts (Send r l ty k) with (isElem (MkRole r) rs)
  synth rs fs ts (Send r l ty k) | (Yes ridx) with (synth rs fs ts k)
    synth rs fs ts (Send r l ty k) | (Yes ridx) | (Yes (lty ** prf))
      = Yes (Comm SEND ridx [B l ty lty] ** Send ridx prf)
    synth rs fs ts (Send r l ty k) | (Yes ridx) | (No no)
      = No (\case ((Comm SEND idx [B l _ ty]) ** (Send prf cont)) => no (ty ** cont))

  synth rs fs ts (Send r l ty k) | (No no)
    = No (\case ((Comm SEND idx [B l bty ty]) ** (Send prf cont)) => no prf)

synth rs fs ts (Recv r xs) with (isElem (MkRole r) rs)
  synth rs fs ts (Recv r xs) | (Yes ridx) with (synth rs fs ts xs)
    synth rs fs ts (Recv r xs) | (Yes ridx) | (Yes (fst ** snd))
      = Yes (Comm RECV _ fst ** Recv ridx snd)

    synth rs fs ts (Recv r xs) | (Yes ridx) | (No no)
      = No (\case ((Comm RECV idx tys) ** (Recv idx bs)) => no (tys ** bs))

  synth rs fs ts (Recv r xs) | (No no)
    = No (\case ((Comm RECV idx tys) ** (Recv idx bs)) => no idx)

synth rs fs ts (If c tt ff) with (check ts BOOL c)
  synth rs fs ts (If c tt ff) | (Yes cond) with (synth rs fs ts tt)
    synth rs fs ts (If c tt ff) | (Yes cond) | (Yes (tyL ** pL)) with (synth rs fs ts ff)
      synth rs fs ts (If c tt ff) | (Yes cond) | (Yes (tyL ** pL)) | (Yes (tyR ** pR)) with (merge tyL tyR)
        synth rs fs ts (If c tt ff) | (Yes cond) | (Yes (tyL ** pL)) | (Yes (tyR ** pR)) | (Yes (ty ** prf))
          = Yes (ty ** If tyL tyR cond pL pR prf)
        synth rs fs ts (If c tt ff) | (Yes cond) | (Yes (tyL ** pL)) | (Yes (tyR ** pR)) | (No no)
          = No (\case (fst ** (If tyL tyR x y z prf)) => no (fst ** ?condMerge))
      synth rs fs ts (If c tt ff) | (Yes cond) | (Yes (tyL ** pL)) | (No no)
        = No (\case (fst ** (If _ _ _ y z _)) => no (_ ** z))
    synth rs fs ts (If c tt ff) | (Yes cond) | (No no)
      = No (\case (fst ** (If _ _ x_ y z _)) => no (_ ** y))

  synth rs fs ts (If c tt ff) | (No no)
    = No (\case (fst ** (If _ _ cond x y prf)) => no cond)

synth rs fs ts (The tytm tm) with (synth rs fs tytm)
  synth rs fs ts (The tytm tm) | (Yes (ty ** pTT)) with (check rs fs ts ty tm)
    synth rs fs ts (The tytm tm) | (Yes (ty ** pTT)) | (Yes tm')
      = Yes (ty ** The ty pTT tm')

    synth rs fs ts (The tytm tm) | (Yes (ty ** pTT)) | (No no)
      = No (checkFails pTT no)
      --(\case (ty ** (The ty x y)) => no ?theTyTy)

  synth rs fs ts (The tytm tm) | (No no)
    = No (\case (fst ** (The fst x y)) => no (fst ** x))

check rs fs ts ty (Switch tm) with (synth rs fs ts tm)
  check rs fs ts ty (Switch tm) | (Yes (tySyn ** prf)) with (subset tySyn ty)
    check rs fs ts ty (Switch tm) | (Yes (tySyn ** prf)) | (Yes prfS)
      = Yes (Switch tySyn prf prfS)
    check rs fs ts ty (Switch tm) | (Yes (tySyn ** prf)) | (No no)
      = No (\case (Switch ty x y) => no ?checkSynSubset)
  check rs fs ts ty (Switch tm) | (No no)
    = No (\case (Switch ty x y) => no (_ ** x))

namespace Session
  public export
  data Check : (rs : SnocList Role)
            -> (ts : SnocList (String,Base))
            -> (tm : Session.AST)
                  -> Type
    where
      Session : Local rs Lin tmty tyExp
             -> Synth rs Lin ts tm tySyn
             -> Subset tySyn tyExp
             -> Check rs ts (Session tmty tm)
             -- here we can do projection...



-- [ EOF ]
