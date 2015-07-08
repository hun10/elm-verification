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


newId : M Int
newId ctx =
  let id = ctx.lastId + 1 in
    (id, { ctx | lastId <- id })


error : (Spec, Impl) -> M Bool
error msg ctx =
  (False, { ctx | errors <- ctx.errors ++ [msg] })


type Type
  = Nat Id


type Predicate
  = Suc (Type, Type)


suc (x, y) =
  case (x, y) of
    (Prim (Nat x), Prim (Nat y)) ->
      Pred (Suc (Nat x, Nat y))

    otherwise ->
      Error


type Spec
  = Prim Type
  | Error
  | Pred Predicate
  | Conj (List Spec)
  | Imp Spec Spec
  | All (Id -> Type) (Spec -> Spec)
  | Exists (Id -> Type) (Spec -> Spec)


type Impl
  = IPrim Type
  | IPred Predicate
  | IError
  | IList (List (M Impl))
  | IFun (Impl -> M Impl)


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
    
    Imp s1 s2 ->
      unit <| IFun (\arg ->
        check (s1, unit arg) *> \chk ->
          if chk then
            mock s2
          else
            unit IError)
    
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
          unit <| IList [unit <| IPrim t, mock <| specC (Prim t)]

check : (Spec, M Impl) -> M Bool
check (spec, impl) =
  case spec of
    Prim t ->
      impl *> \x -> case x of
        IPrim t' ->
          if t == t' then
            unit True
          else
            error (spec, x)
        
        otherwise ->
          error (spec, x)
    
    Pred p ->
      impl *> \x -> case x of
        IPred p' ->
          if p == p' then
            unit True
          else
            error (spec, x)
        
        otherwise ->
          error (spec, x)
    
    Conj lst ->
      impl *> \x -> case x of
        IList lst' ->
          if List.length lst == List.length lst' then
            List.map2 (,) lst lst' |>
              List.map check |>
                foldM (&&) (unit True)
          else
            error (spec, x)
        
        otherwise ->
          error (spec, x)
    
    Imp s1 s2 ->
      impl *> \x -> case x of
        IFun fun ->
          mock s1 *> fun *> \r ->
            check (s2, unit r)
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
        IList [mp, i] ->
          mp *> \(IPrim t) ->
            let s = sc (Prim t) in
              check (s, i)
        
        otherwise ->
          error (spec, x)


spec = All Nat (\x ->
                  Conj [ Exists Nat (\y -> suc (x, y))
                       , Exists Nat (\y -> suc (x, y))
                       ]
               )


axiom = All Nat (\x -> Exists Nat (\y -> suc (x, y)))


axiom2 = All Nat (\x -> suc (x, x))


theorem = Imp axiom spec


call mImpl arg =
  mImpl *> \(IFun fun) ->
    fun arg


func closure =
  unit <|
    IFun closure


list lst =
  unit <| IList lst


exists witness evidence =
  unit <| IList [unit witness, evidence]


byhand =
  func <|
    \(IFun axiom) ->
      func <|
        \x ->
          list [axiom x, axiom x]


main = show <|
  (check (theorem, byhand)
  ) { lastId = 0, errors = [] }
