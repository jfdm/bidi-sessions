module Sessions.Elab

import Sessions.Types.Local
import Sessions.Types.Local.Subset
import Sessions.Types.Local.Merge.Synthesis
import Sessions.AST

import public Sessions.Elab.Expr
import public Sessions.Elab.Local
import public Sessions.Elab.Terms

%default total

namespace Session
  public export
  data Check : (rs : SnocList Role)
            -> (tm : Session.AST)
                  -> Type
    where
      Session : {tyExp,tySyn : _}
             -> Local rs Lin tmty tyExp
             -> Synth rs Lin Lin tm tySyn
             -> Subset tySyn tyExp
             -> Check rs (Session tmty tm)
             -- here we can do projection...


  subsetFails : (Subset tySyn tyExp -> Void)
             -> Local rs [<] tmty tyExp
             -> Synth rs [<] [<] tm tySyn
             -> Check rs (Session tmty tm) -> Void
  subsetFails f tyX tmX (Session tyY tmY prf) with (unique tyX tyY)
    subsetFails f tyX tmX (Session tyY tmY prf) | Refl with (unique tmX tmY)
      subsetFails f tyX tmX (Session tyY tmY prf) | Refl | Refl = f prf

  export
  check : (rs : SnocList Role)
       -> (tm : Session.AST)
             -> Dec (Check rs tm)
  check rs (Session tmty tm) with (synth rs Lin tmty)
    check rs (Session tmty tm) | (Yes (tyExp ** prfTy)) with (synth rs Lin Lin tm)
      check rs (Session tmty tm) | (Yes (tyExp ** prfTy)) | (Yes (tySyn ** prfTm)) with (subset tySyn tyExp)
        check rs (Session tmty tm) | (Yes (tyExp ** prfTy)) | (Yes (tySyn ** prfTm)) | (Yes prf)
          = Yes (Session prfTy prfTm prf)
        check rs (Session tmty tm) | (Yes (tyExp ** prfTy)) | (Yes (tySyn ** prfTm)) | (No no)
          = No (subsetFails no prfTy prfTm)
      check rs (Session tmty tm) | (Yes (tyExp ** prfTy)) | (No no)
        = No $ \case (Session ty tm prf) => no (_ ** tm)
    check rs (Session tmty tm) | (No no)
      = No $ \case (Session ty _ _) => no (_ ** ty)


-- [ EOF ]
