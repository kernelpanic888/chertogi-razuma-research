import IntrinsicNonradialShearRationalMeasurementTable

namespace BoundaryOfSelf.IntrinsicNonradialShearCanonicalReplay

noncomputable section

open IntrinsicNonradialShearRationalParameterRefinement
open IntrinsicNonradialShearRationalMeasurementTable

/-! ## IF-BS-22F-F8C31E: canonical wire format and replay verifier -/

/-- Proof-free external representation of one reduced rational number. -/
structure CanonicalRational where
  numerator : Int
  denominator : Nat
  deriving Repr, DecidableEq

def CanonicalRational.Valid (wire : CanonicalRational) : Prop :=
  wire.denominator ≠ 0 ∧
    wire.numerator.natAbs.Coprime wire.denominator

def CanonicalRational.accepted (wire : CanonicalRational) : Bool :=
  wire.denominator != 0 &&
    decide (wire.numerator.natAbs.Coprime wire.denominator)

def CanonicalRational.encode (value : Rat) : CanonicalRational where
  numerator := value.num
  denominator := value.den

def CanonicalRational.decode (wire : CanonicalRational) : Rat :=
  if hden : wire.denominator ≠ 0 then
    if hred : wire.numerator.natAbs.Coprime wire.denominator then
      Rat.mk' wire.numerator wire.denominator hden hred
    else 0
  else 0

theorem CanonicalRational.encode_valid (value : Rat) :
    (CanonicalRational.encode value).Valid :=
  ⟨value.den_nz, value.reduced⟩

theorem CanonicalRational.encode_accepted (value : Rat) :
    (CanonicalRational.encode value).accepted = true := by
  rw [CanonicalRational.accepted]
  rw [Bool.and_eq_true]
  constructor
  · simpa [CanonicalRational.accepted, CanonicalRational.encode] using
      value.den_nz
  · exact decide_eq_true_eq.mpr value.reduced

theorem CanonicalRational.accepted_eq_true_iff
    (wire : CanonicalRational) :
    wire.accepted = true ↔ wire.Valid := by
  simp [CanonicalRational.accepted, CanonicalRational.Valid]

theorem CanonicalRational.decode_encode (value : Rat) :
    (CanonicalRational.encode value).decode = value := by
  unfold CanonicalRational.decode CanonicalRational.encode
  rw [dif_pos value.den_nz, dif_pos value.reduced]

def CanonicalRational.render (wire : CanonicalRational) : String :=
  toString wire.numerator ++ "/" ++ toString wire.denominator

/-- Proof-free row carried by the interchange document. -/
structure RationalMeasurementWireRow where
  level : Nat
  nodeId : Nat
  hemisphere : Bool
  tIndex : Nat
  vIndex : Nat
  serializedT : CanonicalRational
  serializedV : CanonicalRational
  directionX : CanonicalRational
  directionY : CanonicalRational
  slope : CanonicalRational
  forwardMeasured : CanonicalRational
  inverseMeasured : CanonicalRational
  instrumentNoise : CanonicalRational
  computationalResolution : CanonicalRational
  deriving Repr, DecidableEq

def encodeWireRow {level : Nat}
    (record : ExactRationalMeasurementRecord level) :
    RationalMeasurementWireRow where
  level := level
  nodeId := record.nodeId
  hemisphere := record.node.hemisphere
  tIndex := record.node.tIndex.val
  vIndex := record.node.vIndex.val
  serializedT := CanonicalRational.encode record.serializedT
  serializedV := CanonicalRational.encode record.serializedV
  directionX := CanonicalRational.encode record.directionX
  directionY := CanonicalRational.encode record.directionY
  slope := CanonicalRational.encode record.slope
  forwardMeasured := CanonicalRational.encode record.forwardMeasured
  inverseMeasured := CanonicalRational.encode record.inverseMeasured
  instrumentNoise := CanonicalRational.encode record.instrumentNoise
  computationalResolution :=
    CanonicalRational.encode record.computationalResolution

/-- Recompute one external row from its finite indices and compare every field. -/
def replayWireRowAccepted
    (amplitude : Rat) (row : RationalMeasurementWireRow) : Bool :=
  if ht : row.tIndex < row.level + 2 then
    if hv : row.vIndex < row.level + 2 then
      let node : RationalParameterNode row.level :=
        { hemisphere := row.hemisphere
          tIndex := ⟨row.tIndex, ht⟩
          vIndex := ⟨row.vIndex, hv⟩ }
      row == encodeWireRow (exactRationalMeasurementRecord amplitude node)
    else false
  else false

theorem generated_wireRow_replayAccepted {level : Nat}
    (amplitude : Rat) (node : RationalParameterNode level) :
    replayWireRowAccepted amplitude
      (encodeWireRow (exactRationalMeasurementRecord amplitude node)) = true := by
  simp [replayWireRowAccepted, encodeWireRow,
    exactRationalMeasurementRecord]

def canonicalWireRows (level : Nat) (amplitude : Rat) :
    List RationalMeasurementWireRow :=
  ((rationalMeasurementTable level amplitude).map encodeWireRow).mergeSort
    (fun first second => decide (first.nodeId ≤ second.nodeId))

structure RationalMeasurementWireEnvelope where
  schemaVersion : Nat
  level : Nat
  amplitude : CanonicalRational
  rows : List RationalMeasurementWireRow
  deriving Repr, DecidableEq

def encodeWireEnvelope (level : Nat) (amplitude : Rat) :
    RationalMeasurementWireEnvelope where
  schemaVersion := 1
  level := level
  amplitude := CanonicalRational.encode amplitude
  rows := canonicalWireRows level amplitude

/-- Full replay: reject a noncanonical amplitude, then regenerate and compare
the complete versioned envelope. -/
def replayWireEnvelopeAccepted
    (envelope : RationalMeasurementWireEnvelope) : Bool :=
  if envelope.schemaVersion == 1 then
    if envelope.amplitude.accepted then
      envelope == encodeWireEnvelope envelope.level envelope.amplitude.decode
    else false
  else false

theorem generated_wireEnvelope_replayAccepted
    (level : Nat) (amplitude : Rat) :
    replayWireEnvelopeAccepted (encodeWireEnvelope level amplitude) = true := by
  simp [replayWireEnvelopeAccepted, encodeWireEnvelope,
    CanonicalRational.encode_accepted,
    CanonicalRational.decode_encode]

theorem replayWireEnvelopeAccepted_sound
    {envelope : RationalMeasurementWireEnvelope}
    (haccepted : replayWireEnvelopeAccepted envelope = true) :
    envelope.schemaVersion = 1 ∧
      envelope.amplitude.Valid ∧
      envelope = encodeWireEnvelope envelope.level envelope.amplitude.decode := by
  unfold replayWireEnvelopeAccepted at haccepted
  split at haccepted
  · rename_i hversion
    split at haccepted
    · rename_i hamplitude
      have hvalid : envelope.amplitude.Valid := by
        exact (CanonicalRational.accepted_eq_true_iff _).mp hamplitude
      have heq :
          envelope = encodeWireEnvelope envelope.level envelope.amplitude.decode := by
        exact beq_iff_eq.mp haccepted
      exact ⟨beq_iff_eq.mp hversion, hvalid, heq⟩
    · simp at haccepted
  · simp at haccepted

theorem canonicalWireRows_length
    (level : Nat) (amplitude : Rat) :
    (canonicalWireRows level amplitude).length =
      Fintype.card (RationalParameterNode level) := by
  simp [canonicalWireRows, rationalMeasurementTable_length]

def renderWireRow (row : RationalMeasurementWireRow) : String :=
  String.intercalate "|"
    ["ROW", toString row.level, toString row.nodeId,
      if row.hemisphere then "E" else "W",
      toString row.tIndex, toString row.vIndex,
      row.serializedT.render, row.serializedV.render,
      row.directionX.render, row.directionY.render, row.slope.render,
      row.forwardMeasured.render, row.inverseMeasured.render,
      row.instrumentNoise.render, row.computationalResolution.render]

def renderWireHeader (envelope : RationalMeasurementWireEnvelope) : String :=
  String.intercalate "|"
    ["IFBS31E", toString envelope.schemaVersion, toString envelope.level,
      envelope.amplitude.render, toString envelope.rows.length]

/-- Canonical newline-delimited interchange document. -/
def renderWireEnvelope (envelope : RationalMeasurementWireEnvelope) : String :=
  String.intercalate "\n"
    (renderWireHeader envelope :: envelope.rows.map renderWireRow)

theorem generated_render_replayable
    (level : Nat) (amplitude : Rat) :
    replayWireEnvelopeAccepted (encodeWireEnvelope level amplitude) = true ∧
      (encodeWireEnvelope level amplitude).rows.length =
        Fintype.card (RationalParameterNode level) :=
  ⟨generated_wireEnvelope_replayAccepted level amplitude,
    canonicalWireRows_length level amplitude⟩

end

end BoundaryOfSelf.IntrinsicNonradialShearCanonicalReplay
