import Graphics.Element exposing (show)
-- With no disjunction for now.

type alias Id =
  Int

type alias Ctx =
  { lastId : Id
  }

type alias M a =
  Ctx -> (a, Ctx)

unit : a -> M a
unit v ctx = (v, ctx)

newId : M Int
newId ctx =
  let id = ctx.lastId + 1 in
    (id, { ctx | lastId <- id })

(*>) : M a -> (a -> M b) -> M b
(*>) first second ctx = first ctx |> uncurry second

type Type
  = Nat Id

type Predicate
  = Suc (Type, Type)

type Spec
  = Prim Type
  | Error
  | Pred Predicate
  | Conj (List Spec)
  | All (Id -> Type) (Spec -> Spec)
  | Exists (Id -> Type) (Spec -> Spec)

suc (x, y) =
  case (x, y) of
    (Prim (Nat x), Prim (Nat y)) ->
      Pred (Suc (Nat x, Nat y))

    otherwise ->
      Error

type Impl
  = IPrim Type
  | IPred Predicate
  | IError
  | IList (List (M Impl))
  | IFun (Impl -> M Impl)
  | IWitness Impl (M Impl)

mock : Spec -> M Impl
mock spec =
  case spec of
    Prim t ->
      unit <| IPrim t
    
    Pred p ->
      unit <| IPred p
    
    Conj list ->
      unit <| IList
        (List.map mock list)
    
    All typeC specC ->
      unit <| IFun (\arg ->
        case arg of
          IPrim t ->
            mock <| specC (Prim t)
          
          otherwise ->
            unit IError)
    
    Exists typeC specC ->
      newId *> \id ->
        let t = typeC id in
          unit <| IWitness (IPrim t) (mock <| specC (Prim t))

spec = All Nat (\x ->
                  Conj [ Exists Nat (\y -> suc (x, y))
                       , Exists Nat (\y -> suc (y, y))
                       ]
               )

mocked = mock spec

main = show <|
  (newId *> (\n -> mocked *>
       (\(IFun x) -> x (IPrim (Nat n)))
     ) *>
     (\(IList [a, b]) ->
       a *> (\(IWitness w x) ->
         b *> (\(IWitness w' x') ->
           x
         )
       )
     )
  ) { lastId = 0 }
