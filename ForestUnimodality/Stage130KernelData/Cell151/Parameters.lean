import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage130KernelData.Cell151
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := 68
  A := (-18625856578353600545483459/10000000000000000000000000)
  B := (13033007305237082062987497/100000000000000000000000000)
  C := (53241346166799149303150429/10000000000000000000000000000)
  dδ := (73106512168258711015234041/1000000000000000000000000000)
  dM := (8271419668298529270095143/5000000000000000000000000000)
  wL := 0
  wR := 0
  wC := 1
  price := ![(1939501358255563356891571/125000000000000000000000), (25276815549284279427411093/500000000000000000000000)]
  retention := ![(3/5), (1/100)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (95449/180624)
  hi := (47737/90312)
  vmin := (2032402775/8156257344)
  damping := (2032402775/8156257344)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage130KernelData.Cell151
