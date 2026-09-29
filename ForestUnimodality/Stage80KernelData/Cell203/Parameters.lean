import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage80KernelData.Cell203
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := 45
  A := (-10945457888258313572293901/10000000000000000000000000)
  B := (17563084911704507362628647/100000000000000000000000000)
  C := (36316863647530894798620693/100000000000000000000000000)
  dδ := (2864854503229339113823393/25000000000000000000000000)
  dM := (35546862583495657424148551/10000000000000000000000000000)
  wL := 0
  wR := 1
  wC := 0
  price := ![(93500706472347321351890059/10000000000000000000000000), (43214240693196535048059559/5000000000000000000000000)]
  retention := ![(7/20), (3/10)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (13/23)
  hi := (21/37)
  vmin := (336/1369)
  damping := (336/1369)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage80KernelData.Cell203
