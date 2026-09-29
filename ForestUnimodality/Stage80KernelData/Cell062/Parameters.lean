import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage80KernelData.Cell062
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 3) where
  terms := Finset.univ
  scale := 35
  A := (17257130178539577636342983/10000000000000000000000000)
  B := (-2002620071023681475042011/200000000000000000000000000)
  C := (-11989163537047830849352481/5000000000000000000000000000)
  dδ := (5231436825458452705150947/50000000000000000000000000)
  dM := (12114418841937854131457497/20000000000000000000000000000)
  wL := 0
  wR := 0
  wC := 1
  price := ![(2822607597974688520281461/500000000000000000000000), (13521778317462587182262723/1000000000000000000000000), (17456498600640173890496953/1000000000000000000000000)]
  retention := ![(4/5), (1/10), (1/20)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (9287/19012)
  hi := (24/49)
  vmin := (90316075/361456144)
  damping := (90316075/361456144)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage80KernelData.Cell062
