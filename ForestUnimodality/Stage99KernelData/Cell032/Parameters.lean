import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage99KernelData.Cell032
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 3) where
  terms := Finset.univ
  scale := 54
  A := (10937860257583745749343507/50000000000000000000000000)
  B := (48913511864432199227614717/1000000000000000000000000000)
  C := (-23724360533536529953291261/5000000000000000000000000000)
  dδ := (88067898852319123625953523/1000000000000000000000000000)
  dM := (18498689782198091471898671/20000000000000000000000000000)
  wL := 0
  wR := 0
  wC := 1
  price := ![(2548237318193568579083319/1250000000000000000000000), (55842601290060249752400523/10000000000000000000000000), (46512594194845171102770109/1000000000000000000000000)]
  retention := ![(4/5), (7/10), (1/1000)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (841/1786)
  hi := (1687/3572)
  vmin := (794745/3189796)
  damping := (794745/3189796)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage99KernelData.Cell032
