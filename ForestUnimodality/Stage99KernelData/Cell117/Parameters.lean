import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage99KernelData.Cell117
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 3) where
  terms := Finset.univ
  scale := 60
  A := (-42116720098683593286992277/50000000000000000000000000)
  B := (88040752118994855535127897/1000000000000000000000000000)
  C := (21772033334053423475618061/5000000000000000000000000000)
  dδ := (78612276729427804644600997/1000000000000000000000000000)
  dM := (388585467058650537927611/312500000000000000000000000)
  wL := 0
  wR := 0
  wC := 1
  price := ![(90291063422309978392377161/10000000000000000000000000), (64489989929019015946209947/10000000000000000000000000), (43605312392830803958077013/1000000000000000000000000)]
  retention := ![(7/10), (1/20), (1/100)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (11/21)
  hi := (1549/2954)
  vmin := (2176345/8726116)
  damping := (2176345/8726116)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage99KernelData.Cell117
