import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage130KernelData.Cell045
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := 69
  A := (-15302401117041583466971133/10000000000000000000000000)
  B := (362060084896495331871491/3125000000000000000000000)
  C := (-31134434116642990299228533/10000000000000000000000000000)
  dδ := (75999665051179610131271147/1000000000000000000000000000)
  dM := (2974718496572567247304697/2000000000000000000000000000)
  wL := 0
  wR := 0
  wC := 1
  price := ![(7460509437023057799365233/500000000000000000000000), (52475864792610217079982249/1000000000000000000000000)]
  retention := ![(3/5), (1/1000)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (8999/18624)
  hi := (47/97)
  vmin := (86615375/346853376)
  damping := (86615375/346853376)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage130KernelData.Cell045
