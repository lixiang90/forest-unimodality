import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage80KernelData.Cell166
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 3) where
  terms := Finset.univ
  scale := 101
  A := (-22321830874040376023970111/100000000000000000000000000)
  B := (14723536455242849929625493/100000000000000000000000000)
  C := (81907939791602868417896843/100000000000000000000000000)
  dδ := (1261270416247403311493791/6250000000000000000000000)
  dM := (31556030973348071951012361/10000000000000000000000000000)
  wL := 0
  wR := 1
  wC := 0
  price := ![(36019478738212185042755209/100000000000000000000000000), (1027858412231171669759533/100000000000000000000000), (8883742623159250229036843/250000000000000000000000)]
  retention := ![(4/5), (7/10), (1/20)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (113/213)
  hi := (8069/15194)
  vmin := (57491625/230857636)
  damping := (57491625/230857636)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage80KernelData.Cell166
