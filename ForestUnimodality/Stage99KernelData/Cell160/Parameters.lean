import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage99KernelData.Cell160
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 3) where
  terms := Finset.univ
  scale := 70
  A := (-8639741562454174863994183/12500000000000000000000000)
  B := (2694007919072873707966309/25000000000000000000000000)
  C := (4682167782905616998379017/12500000000000000000000000)
  dδ := (45984784317441414203120331/500000000000000000000000000)
  dM := (1028400666134275133738879/625000000000000000000000000)
  wL := 0
  wR := 1
  wC := 0
  price := ![(13143655482643803011910677/2000000000000000000000000), (70324122577337622175264187/10000000000000000000000000), (16876465763774913142469813/1000000000000000000000000)]
  retention := ![(7/10), (1/10), (1/20)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (97/177)
  hi := (49/89)
  vmin := (1960/7921)
  damping := (1960/7921)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage99KernelData.Cell160
