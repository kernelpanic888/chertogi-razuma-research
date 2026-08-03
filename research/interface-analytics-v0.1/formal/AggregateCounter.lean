import Std

namespace P1AggregateCounter

inductive EventKind where
  | pageView
  | readerOpen
  | languageSwitch
  | supportOpen
deriving Repr, DecidableEq

structure PublicIngress where
  method : String
  route : String
  bodyBytes : Nat
deriving Repr, DecidableEq

structure PrivateMetadata where
  ip : String
  userAgent : String
  referrer : String
  cookie : String
  visitorId : String
deriving Repr, DecidableEq

structure Ingress where
  observable : PublicIngress
  metadata : PrivateMetadata
deriving Repr, DecidableEq

structure SafeEvent where
  day : Nat
  kind : EventKind
deriving Repr, DecidableEq

def decodeRoute (route : String) : Option EventKind :=
  if route == "/e/page-view" then some .pageView
  else if route == "/e/reader-open" then some .readerOpen
  else if route == "/e/language-switch" then some .languageSwitch
  else if route == "/e/support-open" then some .supportOpen
  else none

def sanitize (serverDay : Nat) (request : Ingress) : Option SafeEvent :=
  if request.observable.method == "POST" && request.observable.bodyBytes == 0 then
    (decodeRoute request.observable.route).map fun kind => { day := serverDay, kind := kind }
  else
    none

structure Counts where
  pageView : Nat := 0
  readerOpen : Nat := 0
  languageSwitch : Nat := 0
  supportOpen : Nat := 0
deriving Repr, DecidableEq

def cap : Nat := 2147483647

def satInc (value : Nat) : Nat := min cap (value + 1)

def record (state : Counts) (kind : EventKind) : Counts :=
  match kind with
  | .pageView => { state with pageView := satInc state.pageView }
  | .readerOpen => { state with readerOpen := satInc state.readerOpen }
  | .languageSwitch => { state with languageSwitch := satInc state.languageSwitch }
  | .supportOpen => { state with supportOpen := satInc state.supportOpen }

def process (serverDay : Nat) (state : Counts) (request : Ingress) : Counts :=
  match sanitize serverDay request with
  | some event => record state event.kind
  | none => state

theorem sanitize_metadata_noninterference
    (serverDay : Nat) (observable : PublicIngress) (left right : PrivateMetadata) :
    sanitize serverDay { observable := observable, metadata := left } =
      sanitize serverDay { observable := observable, metadata := right } := by
  rfl

theorem process_metadata_noninterference
    (serverDay : Nat) (state : Counts) (observable : PublicIngress)
    (left right : PrivateMetadata) :
    process serverDay state { observable := observable, metadata := left } =
      process serverDay state { observable := observable, metadata := right } := by
  rfl

theorem satInc_is_bounded (value : Nat) : satInc value <= cap := by
  exact Nat.min_le_left _ _

theorem pageView_record_is_bounded (state : Counts) :
    (record state .pageView).pageView <= cap := by
  exact Nat.min_le_left _ _

end P1AggregateCounter

#print axioms P1AggregateCounter.sanitize_metadata_noninterference
#print axioms P1AggregateCounter.process_metadata_noninterference
#print axioms P1AggregateCounter.satInc_is_bounded
#print axioms P1AggregateCounter.pageView_record_is_bounded
