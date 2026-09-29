import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage130KernelData.Cell018
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 3) where
  terms := Finset.univ
  scale := 39
  A := (9009012587547152673295159/50000000000000000000000000)
  B := (1186706288794176986090001/62500000000000000000000000)
  C := (-67952232168986700933110967/1000000000000000000000000000)
  dδ := (10768219064625241671029343/500000000000000000000000000)
  dM := (14987230328346849315621081/100000000000000000000000000000)
  wL := 1
  wR := 0
  wC := 0
  price := ![(87393625411380859713261771/100000000000000000000000000), (5420627186897762905815057/5000000000000000000000000), (13579698713488753014644317/1000000000000000000000000)]
  retention := ![(4/5), (7/10), (1/100)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (33/85)
  hi := (101/255)
  vmin := (1716/7225)
  damping := (1716/7225)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage130KernelData.Cell018
