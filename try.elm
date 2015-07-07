import Graphics.Element exposing (show)
-- With no disjunction for now.

type alias Id =
  Int

type alias Ctx =
  { lastId : Id
  , errors : List (Spec, Impl)
  }

type alias M a =
  Ctx -> (a, Ctx)

unit : a -> M a
unit v ctx = (v, ctx)

newId : M Int
newId ctx =
  let id = ctx.lastId + 1 in
    (id, { ctx | lastId <- id })

error : (Spec, Impl) -> M Bool
error msg ctx =
  (False, { ctx | errors <- ctx.errors ++ [msg] })

(*>) : M a -> (a -> M b) -> M b
(*>) first second ctx = first ctx |> uncurry second

lift : (a -> b -> c) -> (M a -> M b -> M c)
lift simple =
  \a -> \b ->
    a *> \x ->
      b *> \y ->
        unit (simple x y)

foldM : (a -> b -> b) -> M b -> List (M a) -> M b
foldM folder start list =
  List.foldl (lift folder) start list

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

check : (Spec, M Impl) -> M Bool
check (spec, impl) =
  case spec of
    Prim t ->
      impl *> \x -> case x of
        IPrim t' ->
          unit (t == t')
        otherwise ->
          error (spec, x)
    
    Pred p ->
      impl *> \x -> case x of
        IPred p' ->
          unit (p == p')
        otherwise ->
          error (spec, x)
    
    Conj lst ->
      impl *> \x -> case x of
        IList lst' ->
          List.map2 (,) lst lst' |>
            List.map check |>
              foldM (&&) (unit True)
        otherwise ->
          error (spec, x)
    
    All tc sc ->
      impl *> \x -> case x of
        IFun fun ->
          newId *> \id ->
            let v = tc id
                s = sc (Prim v) in
              check (s, fun (IPrim v))
        otherwise ->
          error (spec, x)
    
    Exists tc sc ->
      impl *> \x -> case x of
        IWitness (IPrim t) i ->
          let s = sc (Prim t) in
            check (s, i)
        otherwise ->
          error (spec, x)


spec = All Nat (\x ->
                  Conj [ Exists Nat (\y -> suc (x, y))
                       , Exists Nat (\y -> suc (y, y))
                       ]
               )

mocked = mock spec

main = show <|
  (check (spec, mocked)
  ) { lastId = 0, errors = [] }
