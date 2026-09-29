import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage130KernelData.Cell145
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := 68
  A := (-9355992903148974920668479/5000000000000000000000000)
  B := (3275774267327568461949383/25000000000000000000000000)
  C := (26370236325893776398177071/5000000000000000000000000000)
  dδ := (571250794791579481757271/7812500000000000000000000)
  dM := (16667265269342998977586401/10000000000000000000000000000)
  wL := 0
  wR := 0
  wC := 1
  price := ![(3857663327992202795257981/250000000000000000000000), (50630312052929909327758651/1000000000000000000000000)]
  retention := ![(3/5), (1/100)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (94503/178928)
  hi := (28/53)
  vmin := (700/2809)
  damping := (700/2809)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage130KernelData.Cell145
