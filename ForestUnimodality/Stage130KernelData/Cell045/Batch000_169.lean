import ForestUnimodality.FiniteKernelSequentialResidual
import ForestUnimodality.Stage130KernelData.Cell045.Parameters
import ForestUnimodality.BinomialMassData.Q8999_18624.Batch000_049
import ForestUnimodality.BinomialMassData.Q8999_18624.Batch050_099
import ForestUnimodality.BinomialMassData.Q8999_18624.Batch100_149
import ForestUnimodality.BinomialMassData.Q8999_18624.Batch150_199
import ForestUnimodality.BinomialMassData.Q47_97.Batch000_049
import ForestUnimodality.BinomialMassData.Q47_97.Batch050_099
import ForestUnimodality.BinomialMassData.Q47_97.Batch100_149
import ForestUnimodality.BinomialMassData.Q47_97.Batch150_199

namespace ForestUnimodality.Stage130KernelData.Cell045.Kernel000
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 0 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree000.table
  base := (689271237783604910254098283/10000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (138)
      previous := (69)
      next := (69)
      square := (759996650511796101312711470000000000000)
      linear := (31134434116642990299228533000000000000)
      constant := (689271237783604910254098283000000000000000) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree000.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 0 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree000.table
  base := (689271237783604910254098283/10000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (138)
      previous := (69)
      next := (69)
      square := (759996650511796101312711470000000000000)
      linear := (31134434116642990299228533000000000000)
      constant := (689271237783604910254098283000000000000000) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree000.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 0 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 0 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell045.Kernel000

namespace ForestUnimodality.Stage130KernelData.Cell045.Kernel001
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 1 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree001.table
  base := (16239280808462361778607865538443643369641/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 846810000000000000000000000000000000000000000
      center := (11685978)
      previous := (5842989)
      next := (5842989)
      square := (64357276361989405655261719991070000000000000)
      linear := (-59557569630352775459486945499909187500000000)
      constant := (34392715406672372430510968383472170233032206775) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree001.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 1 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree001.table
  base := (202599097811982297864159782576557408529447/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1298442)
      previous := (649221)
      next := (649221)
      square := (7150808484665489517251302221230000000000000)
      linear := (-6636705568763062956043861916463000000000000)
      constant := (3814046713341725663402784385280940313707133646) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree001.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 1 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 1 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell045.Kernel001

namespace ForestUnimodality.Stage130KernelData.Cell045.Kernel002
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (49971746941548789863/100000000000000000000)
  directionHi := (6246468367693598733/12500000000000000000)

def endpointA : IntegerEndpointWitness 2 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree002.table
  base := (6264202271061447581135413479526700048137/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 846810000000000000000000000000000000000000000
      center := (11685978)
      previous := (5842989)
      next := (5842989)
      square := (64357276361989405655261719991070000000000000)
      linear := (-121751634276136995980502862402791375000000000)
      constant := (21275912188893015400854834773824330765973446880) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree002.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 2 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree002.table
  base := (15606985752080234427655971216408389644227/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1298442)
      previous := (649221)
      next := (649221)
      square := (7150808484665489517251302221230000000000000)
      linear := (-13566355028129619807813165099923000000000000)
      constant := (2355969509694813491242691283588010610600509488) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree002.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 2 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 2 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell045.Kernel002

namespace ForestUnimodality.Stage130KernelData.Cell045.Kernel003
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (49971746941548789863/100000000000000000000)
  centralHi := (6246468367693598733/12500000000000000000)
  directionLo := (70670722260214531273/100000000000000000000)
  directionHi := (35335361130107265637/50000000000000000000)

def endpointA : IntegerEndpointWitness 3 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree003.table
  base := (162929666207149941562247263105507734301893/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1298442)
      previous := (649221)
      next := (649221)
      square := (7150808484665489517251302221230000000000000)
      linear := (-20438410991324579611279864367297062500000000)
      constant := (1547606474384906036817872824387653994214479987) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree003.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 3 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree003.table
  base := (162209900655519440180940525332368562357169/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1298442)
      previous := (649221)
      next := (649221)
      square := (7150808484665489517251302221230000000000000)
      linear := (-20496004487496176659582468283383000000000000)
      constant := (1540916623021194104774344870941484803218603121) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree003.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 3 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 3 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell045.Kernel003

namespace ForestUnimodality.Stage130KernelData.Cell045.Kernel004
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (70670722260214531273/100000000000000000000)
  centralHi := (35335361130107265637/50000000000000000000)
  directionLo := (17310720929147431093/20000000000000000000)
  directionHi := (43276802322868577733/50000000000000000000)

def endpointA : IntegerEndpointWitness 4 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree004.table
  base := (6979111678695493173496489253368855926589/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 846810000000000000000000000000000000000000000
      center := (11685978)
      previous := (5842989)
      next := (5842989)
      square := (64357276361989405655261719991070000000000000)
      linear := (-246139763567705437022534696208555750000000000)
      constant := (9691289001496107206346785484438188161699229744) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree004.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 4 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree004.table
  base := (111109585529266253328646610088104212473829/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1298442)
      previous := (649221)
      next := (649221)
      square := (7150808484665489517251302221230000000000000)
      linear := (-27425653946862733511351771466843000000000000)
      constant := (1071723644320003997402935696986864535166257061) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree004.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 4 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 4 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell045.Kernel004

namespace ForestUnimodality.Stage130KernelData.Cell045.Kernel005
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (17310720929147431093/20000000000000000000)
  centralHi := (43276802322868577733/50000000000000000000)
  directionLo := (49971746941548789863/50000000000000000000)
  directionHi := (99943493883097579727/100000000000000000000)

def endpointA : IntegerEndpointWitness 5 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree005.table
  base := (16058487123491768794232283896580846239623/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 846810000000000000000000000000000000000000000
      center := (11685978)
      previous := (5842989)
      next := (5842989)
      square := (64357276361989405655261719991070000000000000)
      linear := (-308333828213489657543550613111437937500000000)
      constant := (7168521326090294535314310728327184225036795065) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree005.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 5 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree005.table
  base := (79872359461345172896191018710549596805431/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1298442)
      previous := (649221)
      next := (649221)
      square := (7150808484665489517251302221230000000000000)
      linear := (-34355303406229290363121074650303000000000000)
      constant := (792780135770621794511384871568576156342300279) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree005.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 5 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 5 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell045.Kernel005

namespace ForestUnimodality.Stage130KernelData.Cell045.Kernel006
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (49971746941548789863/50000000000000000000)
  centralHi := (99943493883097579727/100000000000000000000)
  directionLo := (111740223115720304029/100000000000000000000)
  directionHi := (11174022311572030403/10000000000000000000)

def endpointA : IntegerEndpointWitness 6 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree006.table
  base := (7507929455428519700888589658280918399023/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1298442)
      previous := (649221)
      next := (649221)
      square := (7150808484665489517251302221230000000000000)
      linear := (-41169765873252653118285170001591125000000000)
      constant := (624391138040835732065075707949263772153134256) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree006.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 6 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree006.table
  base := (59744080765459154706793117942736467413621/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1298442)
      previous := (649221)
      next := (649221)
      square := (7150808484665489517251302221230000000000000)
      linear := (-41284952865595847214890377833763000000000000)
      constant := (621718378246678607440363416371805421894759989) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree006.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 6 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 6 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell045.Kernel006

namespace ForestUnimodality.Stage130KernelData.Cell045.Kernel007
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (111740223115720304029/100000000000000000000)
  centralHi := (11174022311572030403/10000000000000000000)
  directionLo := (1912582524410631439/1562500000000000000)
  directionHi := (122405281562280412097/100000000000000000000)

def endpointA : IntegerEndpointWitness 7 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree007.table
  base := (11574180538673687531848341228379561128367/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 846810000000000000000000000000000000000000000
      center := (11685978)
      previous := (5842989)
      next := (5842989)
      square := (64357276361989405655261719991070000000000000)
      linear := (-432721957505058098585582446917202312500000000)
      constant := (4647803822494363238884036274122111162375452458) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree007.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 7 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree007.table
  base := (46048793289298930311517482934478262260709/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1298442)
      previous := (649221)
      next := (649221)
      square := (7150808484665489517251302221230000000000000)
      linear := (-48214602324962404066659681017223000000000000)
      constant := (514542300311096529353837918981146969611010981) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree007.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 7 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 7 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell045.Kernel007

namespace ForestUnimodality.Stage130KernelData.Cell045.Kernel008
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (1912582524410631439/1562500000000000000)
  centralHi := (122405281562280412097/100000000000000000000)
  directionLo := (66106407493395327897/50000000000000000000)
  directionHi := (26442562997358131159/20000000000000000000)

def endpointA : IntegerEndpointWitness 8 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree008.table
  base := (36438531757359048167639144944251628288487/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 846810000000000000000000000000000000000000000
      center := (11685978)
      previous := (5842989)
      next := (5842989)
      square := (64357276361989405655261719991070000000000000)
      linear := (-494916022150842319106598363820084500000000000)
      constant := (4037116828512009714140632963600114228847367647) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree008.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 8 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree008.table
  base := (36241046198441999499495660822795539526257/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1298442)
      previous := (649221)
      next := (649221)
      square := (7150808484665489517251302221230000000000000)
      linear := (-55144251784328960918428984200683000000000000)
      constant := (447301755062794255767747106408827231402552113) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree008.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 8 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 8 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell045.Kernel008

namespace ForestUnimodality.Stage130KernelData.Cell045.Kernel009
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (66106407493395327897/50000000000000000000)
  centralHi := (26442562997358131159/20000000000000000000)
  directionLo := (70670722260214531273/50000000000000000000)
  directionHi := (141341444520429062547/100000000000000000000)

def endpointA : IntegerEndpointWitness 9 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree009.table
  base := (14530607847854366584705544117941324211241/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1298442)
      previous := (649221)
      next := (649221)
      square := (7150808484665489517251302221230000000000000)
      linear := (-61901120755180726625290475635885187500000000)
      constant := (407396059570887351834293313301052119768851888) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree009.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 9 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree009.table
  base := (5780014821406383101904895407587200680803/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1298442)
      previous := (649221)
      next := (649221)
      square := (7150808484665489517251302221230000000000000)
      linear := (-62073901243695517770198287384143000000000000)
      constant := (406628760986248479105930309128046856028377135) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree009.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 9 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 9 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell045.Kernel009

namespace ForestUnimodality.Stage130KernelData.Cell045.Kernel010
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (70670722260214531273/50000000000000000000)
  centralHi := (141341444520429062547/100000000000000000000)
  directionLo := (14991524082464636959/10000000000000000000)
  directionHi := (149915240824646369591/100000000000000000000)

def endpointA : IntegerEndpointWitness 10 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree010.table
  base := (11670154041638215622108653107859361392363/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 846810000000000000000000000000000000000000000
      center := (11685978)
      previous := (5842989)
      next := (5842989)
      square := (64357276361989405655261719991070000000000000)
      linear := (-619304151442410760148630197625848875000000000)
      constant := (3466330349640348907736675226225995162180257406) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree010.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 10 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree010.table
  base := (2320626476706475391629825779239394625979/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1298442)
      previous := (649221)
      next := (649221)
      square := (7150808484665489517251302221230000000000000)
      linear := (-69003550703062074621967590567603000000000000)
      constant := (384811586439990274450686442472164640358364110) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree010.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 10 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 10 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell045.Kernel010

namespace ForestUnimodality.Stage130KernelData.Cell045.Kernel011
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (14991524082464636959/10000000000000000000)
  centralHi := (149915240824646369591/100000000000000000000)
  directionLo := (158024538992847273353/100000000000000000000)
  directionHi := (79012269496423636677/50000000000000000000)

def endpointA : IntegerEndpointWitness 11 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree011.table
  base := (18779986891958201696177274352815396901433/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 846810000000000000000000000000000000000000000
      center := (11685978)
      previous := (5842989)
      next := (5842989)
      square := (64357276361989405655261719991070000000000000)
      linear := (-681498216088194980669646114528731062500000000)
      constant := (3394427563857228135756880485344785132334466623) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree011.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 11 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree011.table
  base := (291671225185460148770936722620360015961/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1298442)
      previous := (649221)
      next := (649221)
      square := (7150808484665489517251302221230000000000000)
      linear := (-75933200162428631473736893751063000000000000)
      constant := (377214795679411589349544916284050912971331136) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree011.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 11 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 11 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell045.Kernel011

namespace ForestUnimodality.Stage130KernelData.Cell045.Kernel012
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (158024538992847273353/100000000000000000000)
  centralHi := (79012269496423636677/50000000000000000000)
  directionLo := (82868767361853674389/50000000000000000000)
  directionHi := (165737534723707348779/100000000000000000000)

def endpointA : IntegerEndpointWitness 12 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree012.table
  base := (301356739668463058651936304453901372917/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1298442)
      previous := (649221)
      next := (649221)
      square := (7150808484665489517251302221230000000000000)
      linear := (-82632475637108800132295781270179250000000000)
      constant := (380488950273291735512035550953739018076302650) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree012.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 12 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree012.table
  base := (1497171273025195402977213796658406582883/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1298442)
      previous := (649221)
      next := (649221)
      square := (7150808484665489517251302221230000000000000)
      linear := (-82862849621795188325506196934523000000000000)
      constant := (380917436998487623396004119305345475383461470) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree012.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 12 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 12 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell045.Kernel012

namespace ForestUnimodality.Stage130KernelData.Cell045.Kernel013
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (82868767361853674389/50000000000000000000)
  centralHi := (165737534723707348779/100000000000000000000)
  directionLo := (173107209291474310931/100000000000000000000)
  directionHi := (43276802322868577733/25000000000000000000)

def endpointA : IntegerEndpointWitness 13 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree013.table
  base := (479885132102493345756003522892351192809/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 846810000000000000000000000000000000000000000
      center := (11685978)
      previous := (5842989)
      next := (5842989)
      square := (64357276361989405655261719991070000000000000)
      linear := (-805886345379763421711677948334495437500000000)
      constant := (3538743207650860253444801875133654424093191975) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree013.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 13 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree013.table
  base := (2978750900526206135883004741717545514719/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1298442)
      previous := (649221)
      next := (649221)
      square := (7150808484665489517251302221230000000000000)
      linear := (-89792499081161745177275500117983000000000000)
      constant := (393985733951127446362191147685840542991964284) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree013.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 13 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 13 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell045.Kernel013

namespace ForestUnimodality.Stage130KernelData.Cell045.Kernel014
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (173107209291474310931/100000000000000000000)
  centralHi := (43276802322868577733/25000000000000000000)
  directionLo := (36035139184452989061/20000000000000000000)
  directionHi := (90087847961132472653/50000000000000000000)

def endpointA : IntegerEndpointWitness 14 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree014.table
  base := (4712260682938892024428782171565757042927/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 846810000000000000000000000000000000000000000
      center := (11685978)
      previous := (5842989)
      next := (5842989)
      square := (64357276361989405655261719991070000000000000)
      linear := (-868080410025547642232693865237377625000000000)
      constant := (3725317398628841305032028527130338007976077574) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree014.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 14 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree014.table
  base := (2338557262440240698319366400526243220023/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1298442)
      previous := (649221)
      next := (649221)
      square := (7150808484665489517251302221230000000000000)
      linear := (-96722148540528302029044803301443000000000000)
      constant := (415077944529461330631865922400027689828785628) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree014.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 14 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 14 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell045.Kernel014

namespace ForestUnimodality.Stage130KernelData.Cell045.Kernel015
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (36035139184452989061/20000000000000000000)
  centralHi := (90087847961132472653/50000000000000000000)
  directionLo := (186977156073844142939/100000000000000000000)
  directionHi := (9348857803692207147/5000000000000000000)

def endpointA : IntegerEndpointWitness 15 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree015.table
  base := (3623251587757435234171864027347517199043/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1298442)
      previous := (649221)
      next := (649221)
      square := (7150808484665489517251302221230000000000000)
      linear := (-103363830519036873639301086904473312500000000)
      constant := (441706393469137837754219121759074570350809924) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree015.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 15 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree015.table
  base := (3593168906740646417034641873768930134723/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1298442)
      previous := (649221)
      next := (649221)
      square := (7150808484665489517251302221230000000000000)
      linear := (-103651797999894858880814106484903000000000000)
      constant := (443224459430604310639095565928128727275217414) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree015.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 15 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 15 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell045.Kernel015

namespace ForestUnimodality.Stage130KernelData.Cell045.Kernel016
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (186977156073844142939/100000000000000000000)
  centralHi := (9348857803692207147/5000000000000000000)
  directionLo := (48384935921377470671/25000000000000000000)
  directionHi := (38707948737101976537/20000000000000000000)

def endpointA : IntegerEndpointWitness 16 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree016.table
  base := (5385838046069350736705184449652009701429/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 846810000000000000000000000000000000000000000
      center := (11685978)
      previous := (5842989)
      next := (5842989)
      square := (64357276361989405655261719991070000000000000)
      linear := (-992468539317116083274725699043142000000000000)
      constant := (4282323240355341326882937459790724458526709149) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree016.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 16 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree016.table
  base := (5334397535174133898830090008624219602673/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1298442)
      previous := (649221)
      next := (649221)
      square := (7150808484665489517251302221230000000000000)
      linear := (-110581447459261415732583409668363000000000000)
      constant := (477701422097271762046448977910873282241550257) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree016.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 16 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 16 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell045.Kernel016

namespace ForestUnimodality.Stage130KernelData.Cell045.Kernel017
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (48384935921377470671/25000000000000000000)
  centralHi := (38707948737101976537/20000000000000000000)
  directionLo := (199886987766195159453/100000000000000000000)
  directionHi := (99943493883097579727/50000000000000000000)

def endpointA : IntegerEndpointWitness 17 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree017.table
  base := (3783461851387166319470167926085167196373/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 846810000000000000000000000000000000000000000
      center := (11685978)
      previous := (5842989)
      next := (5842989)
      square := (64357276361989405655261719991070000000000000)
      linear := (-1054662603962900303795741615946024187500000000)
      constant := (4641212886761291835559321036071541406149030763) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree017.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 17 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree017.table
  base := (3739557452964794850255615907301335364843/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1298442)
      previous := (649221)
      next := (649221)
      square := (7150808484665489517251302221230000000000000)
      linear := (-117511096918627972584352712851823000000000000)
      constant := (517955105710984715943030296238169264447807787) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree017.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 17 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 17 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell045.Kernel017

namespace ForestUnimodality.Stage130KernelData.Cell045.Kernel018
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (199886987766195159453/100000000000000000000)
  centralHi := (99943493883097579727/50000000000000000000)
  directionLo := (206038790936641938389/100000000000000000000)
  directionHi := (20603879093664193839/10000000000000000000)

def endpointA : IntegerEndpointWitness 18 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree018.table
  base := (1196702047668808206779369044808523057043/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1298442)
      previous := (649221)
      next := (649221)
      square := (7150808484665489517251302221230000000000000)
      linear := (-124095185400964947146306392538767375000000000)
      constant := (560903739206360910123501154681982691184310174) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree018.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 18 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree018.table
  base := (2356008964963923879768274756144048001403/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1298442)
      previous := (649221)
      next := (649221)
      square := (7150808484665489517251302221230000000000000)
      linear := (-124440746377994529436122016035283000000000000)
      constant := (563554497136566261161933007768033347645200827) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree018.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 18 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 18 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell045.Kernel018

namespace ForestUnimodality.Stage130KernelData.Cell045.Kernel019
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (206038790936641938389/100000000000000000000)
  centralHi := (20603879093664193839/10000000000000000000)
  directionLo := (10600608339032179691/5000000000000000000)
  directionHi := (212012166780643593821/100000000000000000000)

def endpointA : IntegerEndpointWitness 19 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree019.table
  base := (36857727124696236693385891635117708609/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 846810000000000000000000000000000000000000000
      center := (11685978)
      previous := (5842989)
      next := (5842989)
      square := (64357276361989405655261719991070000000000000)
      linear := (-1179050733254468744837773449751788562500000000)
      constant := (5500018603684792375173874715620230838483718078) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree019.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 19 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree019.table
  base := (143458241107911099288695775248371577273/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1298442)
      previous := (649221)
      next := (649221)
      square := (7150808484665489517251302221230000000000000)
      linear := (-131370395837361086287891319218743000000000000)
      constant := (614160061861038240998669682677532425364493256) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree019.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 19 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 19 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell045.Kernel019

namespace ForestUnimodality.Stage130KernelData.Cell045.Kernel020
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (10600608339032179691/5000000000000000000)
  centralHi := (212012166780643593821/100000000000000000000)
  directionLo := (13613862184399931553/6250000000000000000)
  directionHi := (217821794950398904849/100000000000000000000)

def endpointA : IntegerEndpointWitness 20 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree020.table
  base := (14102856501541373152539263169339922177/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 846810000000000000000000000000000000000000000
      center := (11685978)
      previous := (5842989)
      next := (5842989)
      square := (64357276361989405655261719991070000000000000)
      linear := (-1241244797900252965358789366654670750000000000)
      constant := (5994431592427663449490974009428882796286464296) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree020.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 20 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree020.table
  base := (8587172047194639088140677956829641081/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1298442)
      previous := (649221)
      next := (649221)
      square := (7150808484665489517251302221230000000000000)
      linear := (-138300045296727643139660622402203000000000000)
      constant := (669502169707388070856231353642018100929311290) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree020.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 20 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 20 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell045.Kernel020

namespace ForestUnimodality.Stage130KernelData.Cell045.Kernel021
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (13613862184399931553/6250000000000000000)
  centralHi := (217821794950398904849/100000000000000000000)
  directionLo := (223480446231440608059/100000000000000000000)
  directionHi := (11174022311572030403/5000000000000000000)

def endpointA : IntegerEndpointWitness 21 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree021.table
  base := (-829445116424887328823505023361757494199/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1298442)
      previous := (649221)
      next := (649221)
      square := (7150808484665489517251302221230000000000000)
      linear := (-144826540282893020653311698173061437500000000)
      constant := (725491887943654092004593768271571078717550359) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree021.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 21 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree021.table
  base := (-852251517104364952526272643728893824599/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1298442)
      previous := (649221)
      next := (649221)
      square := (7150808484665489517251302221230000000000000)
      linear := (-145229694756094199991429925585663000000000000)
      constant := (729365562920097643133125280192697838004348009) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree021.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 21 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 21 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell045.Kernel021

namespace ForestUnimodality.Stage130KernelData.Cell045.Kernel022
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (223480446231440608059/100000000000000000000)
  centralHi := (11174022311572030403/5000000000000000000)
  directionLo := (57249828242206329517/25000000000000000000)
  directionHi := (228999312968825318069/100000000000000000000)

def endpointA : IntegerEndpointWitness 22 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree022.table
  base := (-832885859334467962579873260368347621909/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 846810000000000000000000000000000000000000000
      center := (11685978)
      previous := (5842989)
      next := (5842989)
      square := (64357276361989405655261719991070000000000000)
      linear := (-1365632927191821406400821200460435125000000000)
      constant := (7103445393376869735279322336394308533105122942) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree022.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 22 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree022.table
  base := (-13480253128632444491021472152269431193/80000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1298442)
      previous := (649221)
      next := (649221)
      square := (7150808484665489517251302221230000000000000)
      linear := (-152159344215460756843199228769123000000000000)
      constant := (793577794690645980077058692081398115238132875) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree022.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 22 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 22 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell045.Kernel022

namespace ForestUnimodality.Stage130KernelData.Cell045.Kernel023
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (57249828242206329517/25000000000000000000)
  centralHi := (228999312968825318069/100000000000000000000)
  directionLo := (234388269400548709167/100000000000000000000)
  directionHi := (14649266837534294323/6250000000000000000)

def endpointA : IntegerEndpointWitness 23 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree023.table
  base := (-301368831974025853831101209034409178177/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 846810000000000000000000000000000000000000000
      center := (11685978)
      previous := (5842989)
      next := (5842989)
      square := (64357276361989405655261719991070000000000000)
      linear := (-1427826991837605626921837117363317312500000000)
      constant := (7715234052679100941978343803383525160417816454) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree023.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 23 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree023.table
  base := (-30339805954947727851543925790960547427/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1298442)
      previous := (649221)
      next := (649221)
      square := (7150808484665489517251302221230000000000000)
      linear := (-159088993674827313694968531952583000000000000)
      constant := (862000403822137876203863077988517176740748560) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree023.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 23 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 23 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell045.Kernel023

namespace ForestUnimodality.Stage130KernelData.Cell045.Kernel024
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (234388269400548709167/100000000000000000000)
  centralHi := (14649266837534294323/6250000000000000000)
  directionLo := (47931215851457133333/20000000000000000000)
  directionHi := (119828039628642833333/50000000000000000000)

def endpointA : IntegerEndpointWitness 24 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree024.table
  base := (-615376834914669017777932059906516022361/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1298442)
      previous := (649221)
      next := (649221)
      square := (7150808484665489517251302221230000000000000)
      linear := (-165557895164821094160317003807355500000000000)
      constant := (929309452804457556355711587852964797478026755) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree024.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 24 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree024.table
  base := (-3090542829511889333701746905729594799063/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1298442)
      previous := (649221)
      next := (649221)
      square := (7150808484665489517251302221230000000000000)
      linear := (-166018643134193870546737835136043000000000000)
      constant := (934522055438617194405292945241742242535616233) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree024.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 24 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 24 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell045.Kernel024

namespace ForestUnimodality.Stage130KernelData.Cell045.Kernel025
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (47931215851457133333/20000000000000000000)
  centralHi := (119828039628642833333/50000000000000000000)
  directionLo := (1912582524410631439/781250000000000000)
  directionHi := (244810563124560824193/100000000000000000000)

def endpointA : IntegerEndpointWitness 25 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree025.table
  base := (-3673157436239913536057010648225167379851/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 846810000000000000000000000000000000000000000
      center := (11685978)
      previous := (5842989)
      next := (5842989)
      square := (64357276361989405655261719991070000000000000)
      linear := (-1552215121129174067963868951169081687500000000)
      constant := (9048286780022009682418392990594259237337306219) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree025.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 25 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree025.table
  base := (-921157548844614557472739385065313420507/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1298442)
      previous := (649221)
      next := (649221)
      square := (7150808484665489517251302221230000000000000)
      linear := (-172948292593560427398507138319503000000000000)
      constant := (1011053142976088194070463681723756864105798548) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree025.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 25 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 25 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell045.Kernel025

namespace ForestUnimodality.Stage130KernelData.Cell045.Kernel026
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (1912582524410631439/781250000000000000)
  centralHi := (244810563124560824193/100000000000000000000)
  directionLo := (62464683676935987329/25000000000000000000)
  directionHi := (249858734707743949317/100000000000000000000)

def endpointA : IntegerEndpointWitness 26 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree026.table
  base := (-4207494383300909850898171633517902505531/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 846810000000000000000000000000000000000000000
      center := (11685978)
      previous := (5842989)
      next := (5842989)
      square := (64357276361989405655261719991070000000000000)
      linear := (-1614409185774958288484884868071963875000000000)
      constant := (9768085095849171535195308867529177214726004389) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree026.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 26 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree026.table
  base := (-843423208398810553368948618950824664997/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1298442)
      previous := (649221)
      next := (649221)
      square := (7150808484665489517251302221230000000000000)
      linear := (-179877942052926984250276441502963000000000000)
      constant := (1091521504410152726657280092058316453635216135) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree026.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 26 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 26 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell045.Kernel026

namespace ForestUnimodality.Stage130KernelData.Cell045.Kernel027
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (62464683676935987329/25000000000000000000)
  centralHi := (249858734707743949317/100000000000000000000)
  directionLo := (254806912783277843471/100000000000000000000)
  directionHi := (15925432048954865217/6250000000000000000)

def endpointA : IntegerEndpointWitness 27 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree027.table
  base := (-37488972989389615188273740694084767539/80000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1298442)
      previous := (649221)
      next := (649221)
      square := (7150808484665489517251302221230000000000000)
      linear := (-186289250046749167667322309441649562500000000)
      constant := (1169183638592950326371759358447600423383662375) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree027.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 27 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree027.table
  base := (-469417912433027127989624573585718336501/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1298442)
      previous := (649221)
      next := (649221)
      square := (7150808484665489517251302221230000000000000)
      linear := (-186807591512293541102045744686423000000000000)
      constant := (1175869003835283023428592641599420761718620910) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree027.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 27 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 27 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell045.Kernel027

namespace ForestUnimodality.Stage130KernelData.Cell045.Kernel028
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (254806912783277843471/100000000000000000000)
  centralHi := (15925432048954865217/6250000000000000000)
  directionLo := (259660813937211466397/100000000000000000000)
  directionHi := (129830406968605733199/50000000000000000000)

def endpointA : IntegerEndpointWitness 28 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree028.table
  base := (-639257497550133615826980704020324403373/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 846810000000000000000000000000000000000000000
      center := (11685978)
      previous := (5842989)
      next := (5842989)
      square := (64357276361989405655261719991070000000000000)
      linear := (-1738797315066526729526916701877728250000000000)
      constant := (11311564566168068299399660382916767265771267896) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree028.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 28 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree028.table
  base := (-2560399229233199223126513365344540876579/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1298442)
      previous := (649221)
      next := (649221)
      square := (7150808484665489517251302221230000000000000)
      linear := (-193737240971660097953815047869883000000000000)
      constant := (1264048793689189094856555386384750429784536378) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree028.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 28 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 28 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell045.Kernel028

namespace ForestUnimodality.Stage130KernelData.Cell045.Kernel029
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (259660813937211466397/100000000000000000000)
  centralHi := (129830406968605733199/50000000000000000000)
  directionLo := (264425629973581311589/100000000000000000000)
  directionHi := (26442562997358131159/10000000000000000000)

def endpointA : IntegerEndpointWitness 29 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree029.table
  base := (-2747679327440530973159319637471099070163/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 846810000000000000000000000000000000000000000
      center := (11685978)
      previous := (5842989)
      next := (5842989)
      square := (64357276361989405655261719991070000000000000)
      linear := (-1800991379712310950047932618780610437500000000)
      constant := (12134477661920129263679427751388876906290772744) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree029.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 29 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree029.table
  base := (-137524672698677567150229818580489557657/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1298442)
      previous := (649221)
      next := (649221)
      square := (7150808484665489517251302221230000000000000)
      linear := (-200666890431026654805584351053343000000000000)
      constant := (1356023116938779155776502876813013950080211480) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree029.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 29 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 29 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell045.Kernel029

namespace ForestUnimodality.Stage130KernelData.Cell045.Kernel030
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (264425629973581311589/100000000000000000000)
  centralHi := (26442562997358131159/10000000000000000000)
  directionLo := (134553046490329915329/50000000000000000000)
  directionHi := (269106092980659830659/100000000000000000000)

def endpointA : IntegerEndpointWitness 30 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree030.table
  base := (-1458320898864325361503660992551362872123/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1298442)
      previous := (649221)
      next := (649221)
      square := (7150808484665489517251302221230000000000000)
      linear := (-207020604928677241174327615075943625000000000)
      constant := (1443457274535672189289922572251210842491653772) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree030.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 30 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree030.table
  base := (-2918989492755210608011355842796240860921/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1298442)
      previous := (649221)
      next := (649221)
      square := (7150808484665489517251302221230000000000000)
      linear := (-207596539890393211657353654236803000000000000)
      constant := (1451761540053701014015018492798850339479188622) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree030.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 30 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 30 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell045.Kernel030

namespace ForestUnimodality.Stage130KernelData.Cell045.Kernel031
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (134553046490329915329/50000000000000000000)
  centralHi := (269106092980659830659/100000000000000000000)
  directionLo := (273706530378260659093/100000000000000000000)
  directionHi := (136853265189130329547/50000000000000000000)

def endpointA : IntegerEndpointWitness 31 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree031.table
  base := (-6130469181230767468139019528274634974809/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 846810000000000000000000000000000000000000000
      center := (11685978)
      previous := (5842989)
      next := (5842989)
      square := (64357276361989405655261719991070000000000000)
      linear := (-1925379509003879391089964452586374812500000000)
      constant := (13881254911014179528215834811634928326616167821) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree031.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 31 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree031.table
  base := (-383398874489255460487659570946674975107/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1298442)
      previous := (649221)
      next := (649221)
      square := (7150808484665489517251302221230000000000000)
      linear := (-214526189349759768509122957420263000000000000)
      constant := (1551239530941934330655934339589076762547491792) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree031.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 31 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 31 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell045.Kernel031

namespace ForestUnimodality.Stage130KernelData.Cell045.Kernel032
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (273706530378260659093/100000000000000000000)
  centralHi := (136853265189130329547/50000000000000000000)
  directionLo := (278230911769515494733/100000000000000000000)
  directionHi := (139115455884757747367/50000000000000000000)

def endpointA : IntegerEndpointWitness 32 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree032.table
  base := (-6389040445287612858924566553356798064669/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 846810000000000000000000000000000000000000000
      center := (11685978)
      previous := (5842989)
      next := (5842989)
      square := (64357276361989405655261719991070000000000000)
      linear := (-1987573573649663611610980369489257000000000000)
      constant := (14804716032572750228327182947546111983085764411) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree032.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 32 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree032.table
  base := (-3196148862486290067654270860732007444527/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1298442)
      previous := (649221)
      next := (649221)
      square := (7150808484665489517251302221230000000000000)
      linear := (-221455838809126325360892260603723000000000000)
      constant := (1654437313785415150845082427243961083908890914) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree032.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 32 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 32 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell045.Kernel032

namespace ForestUnimodality.Stage130KernelData.Cell045.Kernel033
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (278230911769515494733/100000000000000000000)
  centralHi := (139115455884757747367/50000000000000000000)
  directionLo := (282682889040858125093/100000000000000000000)
  directionHi := (141341444520429062547/50000000000000000000)

def endpointA : IntegerEndpointWitness 33 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree033.table
  base := (-206584737520105640955501163777443540909/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1298442)
      previous := (649221)
      next := (649221)
      square := (7150808484665489517251302221230000000000000)
      linear := (-227751959810605314681332920710237687500000000)
      constant := (1751261519358265846254284104148173117729009758) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree033.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 33 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree033.table
  base := (-264536821216393294638453168371319203123/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1298442)
      previous := (649221)
      next := (649221)
      square := (7150808484665489517251302221230000000000000)
      linear := (-228385488268492882212661563787183000000000000)
      constant := (1761338946487654512421081843309075440445392325) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree033.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 33 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 33 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell045.Kernel033

namespace ForestUnimodality.Stage130KernelData.Cell045.Kernel034
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (282682889040858125093/100000000000000000000)
  centralHi := (141341444520429062547/50000000000000000000)
  directionLo := (287065830862672155673/100000000000000000000)
  directionHi := (143532915431336077837/50000000000000000000)

def endpointA : IntegerEndpointWitness 34 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree034.table
  base := (-1699216371216360633662648762025960652459/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 846810000000000000000000000000000000000000000
      center := (11685978)
      previous := (5842989)
      next := (5842989)
      square := (64357276361989405655261719991070000000000000)
      linear := (-2111961702941232052653012203295021375000000000)
      constant := (16751050735901064054321184622272607236378352684) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree034.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 34 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree034.table
  base := (-6799116311105060431836529341924154394077/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1298442)
      previous := (649221)
      next := (649221)
      square := (7150808484665489517251302221230000000000000)
      linear := (-235315137727859439064430866970643000000000000)
      constant := (1871931577267652694539073138073517631306129507) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree034.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 34 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 34 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell045.Kernel034

namespace ForestUnimodality.Stage130KernelData.Cell045.Kernel035
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (287065830862672155673/100000000000000000000)
  centralHi := (143532915431336077837/50000000000000000000)
  directionLo := (291382852517553764767/100000000000000000000)
  directionHi := (9105714141173555149/3125000000000000000)

def endpointA : IntegerEndpointWitness 35 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree035.table
  base := (-1389723525977590225262675995659531160953/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 846810000000000000000000000000000000000000000
      center := (11685978)
      previous := (5842989)
      next := (5842989)
      square := (64357276361989405655261719991070000000000000)
      linear := (-2174155767587016273174028120197903562500000000)
      constant := (17773712753243048600386286781746868364558413785) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree035.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 35 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree035.table
  base := (-6950486205509473676635647448338850309249/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1298442)
      previous := (649221)
      next := (649221)
      square := (7150808484665489517251302221230000000000000)
      linear := (-242244787187225995916200170154103000000000000)
      constant := (1986204845513722268484168847897184757440276159) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree035.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 35 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 35 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell045.Kernel035

namespace ForestUnimodality.Stage130KernelData.Cell045.Kernel036
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (291382852517553764767/100000000000000000000)
  centralHi := (9105714141173555149/3125000000000000000)
  directionLo := (295636841807066866089/100000000000000000000)
  directionHi := (29563684180706686609/10000000000000000000)

def endpointA : IntegerEndpointWitness 36 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree036.table
  base := (-1766716984551931138673652094213377614573/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1298442)
      previous := (649221)
      next := (649221)
      square := (7150808484665489517251302221230000000000000)
      linear := (-248483314692533388188338226344531750000000000)
      constant := (2092140391289668131848405285045782499785430572) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree036.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 36 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree036.table
  base := (-1767104478519307846715740566324998046121/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1298442)
      previous := (649221)
      next := (649221)
      square := (7150808484665489517251302221230000000000000)
      linear := (-249174436646592552767969473337563000000000000)
      constant := (2104150398852290049529650214145780373536190044) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree036.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 36 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 36 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell045.Kernel036

namespace ForestUnimodality.Stage130KernelData.Cell045.Kernel037
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (295636841807066866089/100000000000000000000)
  centralHi := (29563684180706686609/10000000000000000000)
  directionLo := (14991524082464636959/5000000000000000000)
  directionHi := (299830481649292739181/100000000000000000000)

def endpointA : IntegerEndpointWitness 37 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree037.table
  base := (-7152342365829260571889909119755728424837/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 846810000000000000000000000000000000000000000
      center := (11685978)
      previous := (5842989)
      next := (5842989)
      square := (64357276361989405655261719991070000000000000)
      linear := (-2298543896878584714216059954003667937500000000)
      constant := (19917641566312540938924057024420901277955596753) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree037.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 37 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree037.table
  base := (-1430725414576969624789673907940944113457/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1298442)
      previous := (649221)
      next := (649221)
      square := (7150808484665489517251302221230000000000000)
      linear := (-256104086105959109619738776521023000000000000)
      constant := (2225761503863512112167023347736749284182415435) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree037.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 37 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 37 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell045.Kernel037

namespace ForestUnimodality.Stage130KernelData.Cell045.Kernel038
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (14991524082464636959/5000000000000000000)
  centralHi := (299830481649292739181/100000000000000000000)
  directionLo := (303966269869597637979/100000000000000000000)
  directionHi := (15198313493479881899/5000000000000000000)

def endpointA : IntegerEndpointWitness 38 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree038.table
  base := (-360281327299933756615810336144800566901/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 846810000000000000000000000000000000000000000
      center := (11685978)
      previous := (5842989)
      next := (5842989)
      square := (64357276361989405655261719991070000000000000)
      linear := (-2360737961524368934737075870906550125000000000)
      constant := (21038797295350717512115535573843219518182003380) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree038.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 38 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree038.table
  base := (-225209081430804796677895176319662480187/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1298442)
      previous := (649221)
      next := (649221)
      square := (7150808484665489517251302221230000000000000)
      linear := (-263033735565325666471508079704483000000000000)
      constant := (2351032732270851537235308743798399463165456544) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree038.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 38 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 38 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell045.Kernel038

namespace ForestUnimodality.Stage130KernelData.Cell045.Kernel039
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (303966269869597637979/100000000000000000000)
  centralHi := (15198313493479881899/5000000000000000000)
  directionLo := (77011634149826370441/25000000000000000000)
  directionHi := (61609307319861096353/20000000000000000000)

def endpointA : IntegerEndpointWitness 39 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree039.table
  base := (-7227192912723207467719585640814531880833/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1298442)
      previous := (649221)
      next := (649221)
      square := (7150808484665489517251302221230000000000000)
      linear := (-269214669574461461695343531978825812500000000)
      constant := (2465854522504152875647399226220453428419961053) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree039.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 39 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree039.table
  base := (-7228073611026484622846533751061860903439/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1298442)
      previous := (649221)
      next := (649221)
      square := (7150808484665489517251302221230000000000000)
      linear := (-269963385024692223323277382887943000000000000)
      constant := (2479959707964906656908908659767155950759542449) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree039.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 39 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 39 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell045.Kernel039

namespace ForestUnimodality.Stage130KernelData.Cell045.Kernel040
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (77011634149826370441/25000000000000000000)
  centralHi := (61609307319861096353/20000000000000000000)
  directionLo := (7801836490661086751/2500000000000000000)
  directionHi := (312073459626443470041/100000000000000000000)

def endpointA : IntegerEndpointWitness 40 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree040.table
  base := (-1804355645278541155292319790404873517291/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 846810000000000000000000000000000000000000000
      center := (11685978)
      previous := (5842989)
      next := (5842989)
      square := (64357276361989405655261719991070000000000000)
      linear := (-2485126090815937375779107704712314500000000000)
      constant := (23379289514663775453343083666773194466479123316) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree040.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 40 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree040.table
  base := (-451134439755499765080107769871809853391/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1298442)
      previous := (649221)
      next := (649221)
      square := (7150808484665489517251302221230000000000000)
      linear := (-276893034484058780175046686071403000000000000)
      constant := (2612538903064829168134460360182538257431105296) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree040.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 40 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 40 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell045.Kernel040

namespace ForestUnimodality.Stage130KernelData.Cell045.Kernel041
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (7801836490661086751/2500000000000000000)
  centralHi := (312073459626443470041/100000000000000000000)
  directionLo := (316049077985694546707/100000000000000000000)
  directionHi := (79012269496423636677/25000000000000000000)

def endpointA : IntegerEndpointWitness 41 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree041.table
  base := (-7176622998302940383755219430627080570441/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 846810000000000000000000000000000000000000000
      center := (11685978)
      previous := (5842989)
      next := (5842989)
      square := (64357276361989405655261719991070000000000000)
      linear := (-2547320155461721596300123621615196687500000000)
      constant := (24598567696799382672041720922213040685819954429) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree041.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 41 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree041.table
  base := (-1794306287801842555777586655492591647353/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1298442)
      previous := (649221)
      next := (649221)
      square := (7150808484665489517251302221230000000000000)
      linear := (-283822683943425337026815989254863000000000000)
      constant := (2748767473509958367558442820657683820760222492) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree041.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 41 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 41 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell045.Kernel041

namespace ForestUnimodality.Stage130KernelData.Cell045.Kernel042
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (316049077985694546707/100000000000000000000)
  centralHi := (79012269496423636677/25000000000000000000)
  directionLo := (319975304028291883717/100000000000000000000)
  directionHi := (159987652014145941859/50000000000000000000)

def endpointA : IntegerEndpointWitness 42 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree042.table
  base := (-1776260545643316150167988358167396996203/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1298442)
      previous := (649221)
      next := (649221)
      square := (7150808484665489517251302221230000000000000)
      linear := (-289946024456389535202348837613119875000000000)
      constant := (2872278249611990334433509485453448422822778892) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree042.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 42 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree042.table
  base := (-888192454504230481225773840477373091659/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1298442)
      previous := (649221)
      next := (649221)
      square := (7150808484665489517251302221230000000000000)
      linear := (-290752333402791893878585292438323000000000000)
      constant := (2888643126518474581599469150511533172644643752) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree042.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 42 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 42 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell045.Kernel042

namespace ForestUnimodality.Stage130KernelData.Cell045.Kernel043
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (319975304028291883717/100000000000000000000)
  centralHi := (159987652014145941859/50000000000000000000)
  directionLo := (323853934174633757869/100000000000000000000)
  directionHi := (32385393417463375787/10000000000000000000)

def endpointA : IntegerEndpointWitness 43 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree043.table
  base := (-7002880210231864814662935315931864716457/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 846810000000000000000000000000000000000000000
      center := (11685978)
      previous := (5842989)
      next := (5842989)
      square := (64357276361989405655261719991070000000000000)
      linear := (-2671708284753290037342155455420961062500000000)
      constant := (27135082221127636471875618566654738677519923533) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree043.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 43 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree043.table
  base := (-7003290935937069323378140632250182242923/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1298442)
      previous := (649221)
      next := (649221)
      square := (7150808484665489517251302221230000000000000)
      linear := (-297681982862158450730354595621783000000000000)
      constant := (3032164013735894752688837760105707035276337493) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree043.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 43 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 43 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell045.Kernel043

namespace ForestUnimodality.Stage130KernelData.Cell045.Kernel044
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (323853934174633757869/100000000000000000000)
  centralHi := (32385393417463375787/10000000000000000000)
  directionLo := (6553733170423654221/2000000000000000000)
  directionHi := (327686658521182711051/100000000000000000000)

def endpointA : IntegerEndpointWitness 44 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree044.table
  base := (-214696827569458071343184306438094080967/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 846810000000000000000000000000000000000000000
      center := (11685978)
      previous := (5842989)
      next := (5842989)
      square := (64357276361989405655261719991070000000000000)
      linear := (-2733902349399074257863171372323843250000000000)
      constant := (28452287953065221200702317173997183843835771136) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree044.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 44 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree044.table
  base := (-3435318708599872362109761339455311500007/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1298442)
      previous := (649221)
      next := (649221)
      square := (7150808484665489517251302221230000000000000)
      linear := (-304611632321525007582123898805243000000000000)
      constant := (3179328645093864974588127841985741948192868274) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree044.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 44 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 44 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell045.Kernel044

namespace ForestUnimodality.Stage130KernelData.Cell045.Kernel045
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (6553733170423654221/2000000000000000000)
  centralHi := (327686658521182711051/100000000000000000000)
  directionLo := (82868767361853674389/25000000000000000000)
  directionHi := (331475069447414697557/100000000000000000000)

def endpointA : IntegerEndpointWitness 45 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree045.table
  base := (-6707427199640790446052829225019170877977/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1298442)
      previous := (649221)
      next := (649221)
      square := (7150808484665489517251302221230000000000000)
      linear := (-310677379338317608709354143247413937500000000)
      constant := (3311345601862414353926793048445069452752083157) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree045.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 45 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree045.table
  base := (-6707706747731423447061743216578747674697/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1298442)
      previous := (649221)
      next := (649221)
      square := (7150808484665489517251302221230000000000000)
      linear := (-311541281780891564433893201988703000000000000)
      constant := (3330135819365024259406311593778345563128775927) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree045.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 45 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 45 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell045.Kernel045

namespace ForestUnimodality.Stage130KernelData.Cell045.Kernel046
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (82868767361853674389/25000000000000000000)
  centralHi := (331475069447414697557/100000000000000000000)
  directionLo := (41902583668395114011/12500000000000000000)
  directionHi := (335220669347160912089/100000000000000000000)

def endpointA : IntegerEndpointWitness 46 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree046.table
  base := (-6514371394343827705423791056097251685853/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 846810000000000000000000000000000000000000000
      center := (11685978)
      previous := (5842989)
      next := (5842989)
      square := (64357276361989405655261719991070000000000000)
      linear := (-2858290478690642698905203206129607625000000000)
      constant := (31184540718014429845342587958224174956162157107) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree046.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 46 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree046.table
  base := (-6514601847240082856123492079247203187803/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1298442)
      previous := (649221)
      next := (649221)
      square := (7150808484665489517251302221230000000000000)
      linear := (-318470931240258121285662505172163000000000000)
      constant := (3484584568177840248123455362835481065205961573) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree046.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 46 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 46 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell045.Kernel046

namespace ForestUnimodality.Stage130KernelData.Cell045.Kernel047
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (41902583668395114011/12500000000000000000)
  centralHi := (335220669347160912089/100000000000000000000)
  directionLo := (84731219397703693423/25000000000000000000)
  directionHi := (338924877590814773693/100000000000000000000)

def endpointA : IntegerEndpointWitness 47 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree047.table
  base := (-6291215793938444766041858533031665972303/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 846810000000000000000000000000000000000000000
      center := (11685978)
      previous := (5842989)
      next := (5842989)
      square := (64357276361989405655261719991070000000000000)
      linear := (-2920484543336426919426219123032489812500000000)
      constant := (32599571682004862360017045462781243700342378407) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree047.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 47 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree047.table
  base := (-6291405684131815833865990836215288112673/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1298442)
      previous := (649221)
      next := (649221)
      square := (7150808484665489517251302221230000000000000)
      linear := (-325400580699624678137431808355623000000000000)
      constant := (3642674110882580012808481515411611354147859743) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree047.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 47 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 47 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell045.Kernel047

namespace ForestUnimodality.Stage130KernelData.Cell045.Kernel048
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (84731219397703693423/25000000000000000000)
  centralHi := (338924877590814773693/100000000000000000000)
  directionLo := (2740712294479246143/800000000000000000)
  directionHi := (85647259202476441969/25000000000000000000)

def endpointA : IntegerEndpointWitness 48 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree048.table
  base := (-6038028746438996240195858184985150682977/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1298442)
      previous := (649221)
      next := (649221)
      square := (7150808484665489517251302221230000000000000)
      linear := (-331408734220245682216359448881708000000000000)
      constant := (3783021946772758129604586647817866842223869407) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree048.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 48 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree048.table
  base := (-3019092571333264752952489707812175787899/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1298442)
      previous := (649221)
      next := (649221)
      square := (7150808484665489517251302221230000000000000)
      linear := (-332330230158991234989201111539083000000000000)
      constant := (3804403818165242087316471554522854476023316618) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree048.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 48 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 48 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell045.Kernel048

namespace ForestUnimodality.Stage130KernelData.Cell045.Kernel049
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (2740712294479246143/800000000000000000)
  centralHi := (85647259202476441969/25000000000000000000)
  directionLo := (173107209291474310931/50000000000000000000)
  directionHi := (346214418582948621863/100000000000000000000)

def endpointA : IntegerEndpointWitness 49 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree049.table
  base := (-5754865386347523603288458346364531250893/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 846810000000000000000000000000000000000000000
      center := (11685978)
      previous := (5842989)
      next := (5842989)
      square := (64357276361989405655261719991070000000000000)
      linear := (-3044872672627995360468250956838254187500000000)
      constant := (35527413566019544890436717703736944210686098617) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree049.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 49 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree049.table
  base := (-179843566892894394852830656986150369973/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1298442)
      previous := (649221)
      next := (649221)
      square := (7150808484665489517251302221230000000000000)
      linear := (-339259879618357791840970414722543000000000000)
      constant := (3969773182713919986503886870923180957405569376) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree049.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 49 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 49 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell045.Kernel049

namespace ForestUnimodality.Stage130KernelData.Cell045.Kernel050
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (173107209291474310931/50000000000000000000)
  centralHi := (346214418582948621863/100000000000000000000)
  directionLo := (349802228590841529043/100000000000000000000)
  directionHi := (87450557147710382261/25000000000000000000)

def endpointA : IntegerEndpointWitness 50 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree050.table
  base := (-5441770188775388478583339234622007034847/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 846810000000000000000000000000000000000000000
      center := (11685978)
      previous := (5842989)
      next := (5842989)
      square := (64357276361989405655261719991070000000000000)
      linear := (-3107066737273779580989266873741136375000000000)
      constant := (37040216051002122318383767378415601898453996193) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree050.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 50 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree050.table
  base := (-1360469035599116846773229865167036670939/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1298442)
      previous := (649221)
      next := (649221)
      square := (7150808484665489517251302221230000000000000)
      linear := (-346189529077724348692739717906003000000000000)
      constant := (4138781795570696838215582669772223407852539796) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree050.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 50 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 50 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell045.Kernel050

namespace ForestUnimodality.Stage130KernelData.Cell045.Kernel051
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (349802228590841529043/100000000000000000000)
  centralHi := (87450557147710382261/25000000000000000000)
  directionLo := (176676805650536328183/50000000000000000000)
  directionHi := (353353611301072656367/100000000000000000000)

def endpointA : IntegerEndpointWitness 51 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree051.table
  base := (-1019755805977507561317437929553531965711/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1298442)
      previous := (649221)
      next := (649221)
      square := (7150808484665489517251302221230000000000000)
      linear := (-352140089102173755723364754516002062500000000)
      constant := (4287289104208114619823709104476942545216094755) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree051.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 51 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree051.table
  base := (-1019773237141051124800978889549213859139/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1298442)
      previous := (649221)
      next := (649221)
      square := (7150808484665489517251302221230000000000000)
      linear := (-353119178537090905544509021089463000000000000)
      constant := (4311429327067102990669481457597090233996805745) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree051.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 51 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 51 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell045.Kernel051

namespace ForestUnimodality.Stage130KernelData.Cell045.Kernel052
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (176676805650536328183/50000000000000000000)
  centralHi := (353353611301072656367/100000000000000000000)
  directionLo := (178434827116162872503/50000000000000000000)
  directionHi := (356869654232325745007/100000000000000000000)

def endpointA : IntegerEndpointWitness 52 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree052.table
  base := (-4725920849088802380896433337965670970319/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 846810000000000000000000000000000000000000000
      center := (11685978)
      previous := (5842989)
      next := (5842989)
      square := (64357276361989405655261719991070000000000000)
      linear := (-3231454866565348022031298707546900750000000000)
      constant := (40163568776014532194093022629610572196249916761) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree052.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 52 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree052.table
  base := (-118149812864046713926571843300523202207/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1298442)
      previous := (649221)
      next := (649221)
      square := (7150808484665489517251302221230000000000000)
      linear := (-360048827996457462396278324272923000000000000)
      constant := (4487715511454750775732942050264091087617373480) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree052.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 52 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 52 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell045.Kernel052

namespace ForestUnimodality.Stage130KernelData.Cell045.Kernel053
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (178434827116162872503/50000000000000000000)
  centralHi := (356869654232325745007/100000000000000000000)
  directionLo := (360351391844529890611/100000000000000000000)
  directionHi := (90087847961132472653/25000000000000000000)

def endpointA : IntegerEndpointWitness 53 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree053.table
  base := (-4323218989928806654363836678636386043063/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 846810000000000000000000000000000000000000000
      center := (11685978)
      previous := (5842989)
      next := (5842989)
      square := (64357276361989405655261719991070000000000000)
      linear := (-3293648931211132242552314624449782937500000000)
      constant := (41774114588671498417130664337102261482061600847) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree053.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 53 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree053.table
  base := (-4323277896390463724081482224833322572083/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1298442)
      previous := (649221)
      next := (649221)
      square := (7150808484665489517251302221230000000000000)
      linear := (-366978477455824019248047627456383000000000000)
      constant := (4667640134514946295132666641982422267919271053) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree053.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 53 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 53 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell045.Kernel053

namespace ForestUnimodality.Stage130KernelData.Cell045.Kernel054
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (360351391844529890611/100000000000000000000)
  centralHi := (90087847961132472653/25000000000000000000)
  directionLo := (90949952273448209529/25000000000000000000)
  directionHi := (363799809093792838117/100000000000000000000)

def endpointA : IntegerEndpointWitness 54 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree054.table
  base := (-3890692281823916674402014815064373914457/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1298442)
      previous := (649221)
      next := (649221)
      square := (7150808484665489517251302221230000000000000)
      linear := (-372871443984101829230370060150296125000000000)
      constant := (4824137531261124772696151044405523132010749087) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree054.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 54 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree054.table
  base := (-4863425854497707352681528734736641989/12500000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1298442)
      previous := (649221)
      next := (649221)
      square := (7150808484665489517251302221230000000000000)
      linear := (-373908126915190576099816930639843000000000000)
      constant := (4851203023569890912029247143445432348420399200) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree054.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 54 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 54 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell045.Kernel054

namespace ForestUnimodality.Stage130KernelData.Cell045.Kernel055
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (90949952273448209529/25000000000000000000)
  centralHi := (363799809093792838117/100000000000000000000)
  directionLo := (5737747573231894317/1562500000000000000)
  directionHi := (367215844686841236289/100000000000000000000)

def endpointA : IntegerEndpointWitness 55 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree055.table
  base := (-27426847301537380279323276850683185401/80000000000000000000000000000000000000)
  polynomial :=
    { denominator := 846810000000000000000000000000000000000000000
      center := (11685978)
      previous := (5842989)
      next := (5842989)
      square := (64357276361989405655261719991070000000000000)
      linear := (-3418037060502700683594346458255547312500000000)
      constant := (45092937067922318252305185776183670767737708625) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree055.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 55 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree055.table
  base := (-3428395669424547610200100659840628817753/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1298442)
      previous := (649221)
      next := (649221)
      square := (7150808484665489517251302221230000000000000)
      linear := (-380837776374557132951586233823303000000000000)
      constant := (5038404039429993488027380597005224523453762023) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree055.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 55 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 55 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell045.Kernel055

namespace ForestUnimodality.Stage130KernelData.Cell045.Kernel056
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (5737747573231894317/1562500000000000000)
  centralHi := (367215844686841236289/100000000000000000000)
  directionLo := (185300197032720728743/50000000000000000000)
  directionHi := (370600394065441457487/100000000000000000000)

def endpointA : IntegerEndpointWitness 56 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree056.table
  base := (-734055533228630512402779033248755035767/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 846810000000000000000000000000000000000000000
      center := (11685978)
      previous := (5842989)
      next := (5842989)
      square := (64357276361989405655261719991070000000000000)
      linear := (-3480231125148484904115362375158429500000000000)
      constant := (46801211411013575269437612948188470543014858692) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree056.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 56 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree056.table
  base := (-2936254777902034610182624731174147106501/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1298442)
      previous := (649221)
      next := (649221)
      square := (7150808484665489517251302221230000000000000)
      linear := (-387767425833923689803355537006763000000000000)
      constant := (5229243069902032929697546384868630449874932091) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree056.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 56 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 56 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell045.Kernel056

namespace ForestUnimodality.Stage130KernelData.Cell045.Kernel057
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (185300197032720728743/50000000000000000000)
  centralHi := (370600394065441457487/100000000000000000000)
  directionLo := (373954312147688285879/100000000000000000000)
  directionHi := (9348857803692207147/2500000000000000000)

def endpointA : IntegerEndpointWitness 57 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree057.table
  base := (-60357520580612706495072389800476864971/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1298442)
      previous := (649221)
      next := (649221)
      square := (7150808484665489517251302221230000000000000)
      linear := (-393602798866029902737375365784590187500000000)
      constant := (5393562219323721871931238922638110760986233190) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree057.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 57 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree057.table
  base := (-241432762008026497300592550072723916157/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1298442)
      previous := (649221)
      next := (649221)
      square := (7150808484665489517251302221230000000000000)
      linear := (-394697075293290246655124840190223000000000000)
      constant := (5423720024555643192242342864052948406728787870) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree057.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 57 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 57 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell045.Kernel057

namespace ForestUnimodality.Stage130KernelData.Cell045.Kernel058
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (373954312147688285879/100000000000000000000)
  centralHi := (9348857803692207147/2500000000000000000)
  directionLo := (377278415849940821297/100000000000000000000)
  directionHi := (188639207924970410649/50000000000000000000)

def endpointA : IntegerEndpointWitness 58 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree058.table
  base := (-232824994103393282103615767481890784463/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 846810000000000000000000000000000000000000000
      center := (11685978)
      previous := (5842989)
      next := (5842989)
      square := (64357276361989405655261719991070000000000000)
      linear := (-3604619254440053345157394208964193875000000000)
      constant := (50315482081781833103186189578381113456143984576) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree058.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 58 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree058.table
  base := (-465655485608888731216305416843802735317/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1298442)
      previous := (649221)
      next := (649221)
      square := (7150808484665489517251302221230000000000000)
      linear := (-401626724752656803506894143373683000000000000)
      constant := (5621834830504228616289499221820460640253609388) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree058.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 58 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 58 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell045.Kernel058

namespace ForestUnimodality.Stage130KernelData.Cell045.Kernel059
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (377278415849940821297/100000000000000000000)
  centralHi := (188639207924970410649/50000000000000000000)
  directionLo := (190286743205242143559/50000000000000000000)
  directionHi := (380573486410484287119/100000000000000000000)

def endpointA : IntegerEndpointWitness 59 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree059.table
  base := (-160140743620531267393277072867237533059/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 846810000000000000000000000000000000000000000
      center := (11685978)
      previous := (5842989)
      next := (5842989)
      square := (64357276361989405655261719991070000000000000)
      linear := (-3666813319085837565678410125867076062500000000)
      constant := (52121477190353319977181292809365121409403465318) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree059.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 59 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree059.table
  base := (-1281143988362594791741446385629693950021/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1298442)
      previous := (649221)
      next := (649221)
      square := (7150808484665489517251302221230000000000000)
      linear := (-408556374212023360358663446557143000000000000)
      constant := (5823587429003688560561860858120367209624252411) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree059.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 59 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 59 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell045.Kernel059

namespace ForestUnimodality.Stage130KernelData.Cell045.Kernel060
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (190286743205242143559/50000000000000000000)
  centralHi := (380573486410484287119/100000000000000000000)
  directionLo := (383840271533643612803/100000000000000000000)
  directionHi := (95960067883410903201/25000000000000000000)

def endpointA : IntegerEndpointWitness 60 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree060.table
  base := (-334941997521267337073944504537848227923/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1298442)
      previous := (649221)
      next := (649221)
      square := (7150808484665489517251302221230000000000000)
      linear := (-414334153747957976244380671418884250000000000)
      constant := (5995560540076877050683204780575258451734444986) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree060.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 60 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree060.table
  base := (-16747469739880415762750421653308027721/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1298442)
      previous := (649221)
      next := (649221)
      square := (7150808484665489517251302221230000000000000)
      linear := (-415486023671389917210432749740603000000000000)
      constant := (6028977772710439399236286972417740990686924440) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree060.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 60 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 60 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell045.Kernel060

namespace ForestUnimodality.Stage130KernelData.Cell045.Kernel061
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (383840271533643612803/100000000000000000000)
  centralHi := (95960067883410903201/25000000000000000000)
  directionLo := (387079487371019765369/100000000000000000000)
  directionHi := (38707948737101976537/10000000000000000000)

def endpointA : IntegerEndpointWitness 61 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree061.table
  base := (-7219567783128338714956073370354241691/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 846810000000000000000000000000000000000000000
      center := (11685978)
      previous := (5842989)
      next := (5842989)
      square := (64357276361989405655261719991070000000000000)
      linear := (-3791201448377406006720441959672840437500000000)
      constant := (55831184738825002386985915607423823660599176466) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree061.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 61 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree061.table
  base := (-28890401137810606169075626992891907667/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1298442)
      previous := (649221)
      next := (649221)
      square := (7150808484665489517251302221230000000000000)
      linear := (-422415673130756474062202052924063000000000000)
      constant := (6238005823470944825250310041759686880040761197) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree061.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 61 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 61 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell045.Kernel061

namespace ForestUnimodality.Stage130KernelData.Cell045.Kernel062
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (387079487371019765369/100000000000000000000)
  centralHi := (38707948737101976537/10000000000000000000)
  directionLo := (195145910177360391987/50000000000000000000)
  directionHi := (15611672814188831359/4000000000000000000)

def endpointA : IntegerEndpointWitness 62 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree062.table
  base := (320943926011327585715710037387646909333/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 846810000000000000000000000000000000000000000
      center := (11685978)
      previous := (5842989)
      next := (5842989)
      square := (64357276361989405655261719991070000000000000)
      linear := (-3853395513023190227241457876575722625000000000)
      constant := (57734896539314745352281637581372707638280330546) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree062.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 62 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree062.table
  base := (641877909343429057098873226580483806407/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1298442)
      previous := (649221)
      next := (649221)
      square := (7150808484665489517251302221230000000000000)
      linear := (-429345322590123030913971356107523000000000000)
      constant := (6450671550539733617148596885020301772134483463) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree062.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 62 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 62 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell045.Kernel062

namespace ForestUnimodality.Stage130KernelData.Cell045.Kernel063
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (195145910177360391987/50000000000000000000)
  centralHi := (15611672814188831359/4000000000000000000)
  directionLo := (196738964447940403213/50000000000000000000)
  directionHi := (393477928895880806427/100000000000000000000)

def endpointA : IntegerEndpointWitness 63 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree063.table
  base := (134241165650224659479368311279066180853/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1298442)
      previous := (649221)
      next := (649221)
      square := (7150808484665489517251302221230000000000000)
      linear := (-435065508629886049751385977053178312500000000)
      constant := (6630131114667208610749627069203411500530677520) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree063.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 63 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree063.table
  base := (671201754421218257835265779290343955287/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1298442)
      previous := (649221)
      next := (649221)
      square := (7150808484665489517251302221230000000000000)
      linear := (-436274972049489587765740659290983000000000000)
      constant := (6666974929142851701408495890037894692550590766) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree063.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 63 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 63 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell045.Kernel063

namespace ForestUnimodality.Stage130KernelData.Cell045.Kernel064
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (196738964447940403213/50000000000000000000)
  centralHi := (393477928895880806427/100000000000000000000)
  directionLo := (49579805620046495923/12500000000000000000)
  directionHi := (79327688992074393477/20000000000000000000)

def endpointA : IntegerEndpointWitness 64 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree064.table
  base := (2072690950957735833587049068113156073293/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 846810000000000000000000000000000000000000000
      center := (11685978)
      previous := (5842989)
      next := (5842989)
      square := (64357276361989405655261719991070000000000000)
      linear := (-3977783642314758668283489710381487000000000000)
      constant := (61640035031329814367942584025964463169442524533) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree064.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 64 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree064.table
  base := (1036342137966130721053321635508351656387/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1298442)
      previous := (649221)
      next := (649221)
      square := (7150808484665489517251302221230000000000000)
      linear := (-443204621508856144617509962474443000000000000)
      constant := (6886915939319792902399131096186468161469890566) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree064.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 64 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 64 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell045.Kernel064

namespace ForestUnimodality.Stage130KernelData.Cell045.Kernel065
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (49579805620046495923/12500000000000000000)
  centralHi := (79327688992074393477/20000000000000000000)
  directionLo := (399773975532390318907/100000000000000000000)
  directionHi := (99943493883097579727/25000000000000000000)

def endpointA : IntegerEndpointWitness 65 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree065.table
  base := (5532664001502310249135533176505370859/19531250000000000000000000000000000000)
  polynomial :=
    { denominator := 846810000000000000000000000000000000000000000
      center := (11685978)
      previous := (5842989)
      next := (5842989)
      square := (64357276361989405655261719991070000000000000)
      linear := (-4039977706960542888804505627284369187500000000)
      constant := (63641461387690412823320699235512809036489989998) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree065.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 65 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree065.table
  base := (1416359250772128065374920299806217021209/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1298442)
      previous := (649221)
      next := (649221)
      square := (7150808484665489517251302221230000000000000)
      linear := (-450134270968222701469279265657903000000000000)
      constant := (7110494564989930313857972330171948391905110962) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree065.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 65 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 65 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell045.Kernel065

namespace ForestUnimodality.Stage130KernelData.Cell045.Kernel066
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (399773975532390318907/100000000000000000000)
  centralHi := (99943493883097579727/25000000000000000000)
  directionLo := (402885103975516081873/100000000000000000000)
  directionHi := (201442551987758040937/50000000000000000000)

def endpointA : IntegerEndpointWitness 66 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree066.table
  base := (3622509285890527885904865704244968741661/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1298442)
      previous := (649221)
      next := (649221)
      square := (7150808484665489517251302221230000000000000)
      linear := (-455796863511814123258391282687472375000000000)
      constant := (7297273220055225386347056358275196596437163349) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree066.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 66 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree066.table
  base := (905626202245636815960625124389283572533/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1298442)
      previous := (649221)
      next := (649221)
      square := (7150808484665489517251302221230000000000000)
      linear := (-457063920427589258321048568841363000000000000)
      constant := (7337710793199932463738238116746893076535851988) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree066.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 66 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 66 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell045.Kernel066

namespace ForestUnimodality.Stage130KernelData.Cell045.Kernel067
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (402885103975516081873/100000000000000000000)
  centralHi := (201442551987758040937/50000000000000000000)
  directionLo := (405972391299891962287/100000000000000000000)
  directionHi := (25373274456243247643/6250000000000000000)

def endpointA : IntegerEndpointWitness 67 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree067.table
  base := (2221022877288979773341108001916956485077/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 846810000000000000000000000000000000000000000
      center := (11685978)
      previous := (5842989)
      next := (5842989)
      square := (64357276361989405655261719991070000000000000)
      linear := (-4164365836252111329846537461090133562500000000)
      constant := (67742027712557567636022712812473193396237329624) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree067.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 67 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree067.table
  base := (4442042089445300151438093244500585749269/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1298442)
      previous := (649221)
      next := (649221)
      square := (7150808484665489517251302221230000000000000)
      linear := (-463993569886955815172817872024823000000000000)
      constant := (7568564613517082889442221557772527011314872021) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree067.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 67 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 67 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell045.Kernel067

namespace ForestUnimodality.Stage130KernelData.Cell045.Kernel068
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (405972391299891962287/100000000000000000000)
  centralHi := (25373274456243247643/6250000000000000000)
  directionLo := (409036377343315011257/100000000000000000000)
  directionHi := (204518188671657505629/50000000000000000000)

def endpointA : IntegerEndpointWitness 68 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree068.table
  base := (330708278120696466886773181742100500459/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 846810000000000000000000000000000000000000000
      center := (11685978)
      previous := (5842989)
      next := (5842989)
      square := (64357276361989405655261719991070000000000000)
      linear := (-4226559900897895550367553377993015750000000000)
      constant := (69841167505550545086104469438714390491857397264) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree068.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 68 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree068.table
  base := (132283236251174026664426945505071077997/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1298442)
      previous := (649221)
      next := (649221)
      square := (7150808484665489517251302221230000000000000)
      linear := (-470923219346322372024587175208283000000000000)
      constant := (7803056017540221415952960331789412550914950920) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree068.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 68 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 68 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell045.Kernel068

namespace ForestUnimodality.Stage130KernelData.Cell045.Kernel069
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (409036377343315011257/100000000000000000000)
  centralHi := (204518188671657505629/50000000000000000000)
  directionLo := (206038790936641938389/50000000000000000000)
  directionHi := (412077581873283876779/100000000000000000000)

def endpointA : IntegerEndpointWitness 69 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree069.table
  base := (385648039173158716002408636898830797649/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1298442)
      previous := (649221)
      next := (649221)
      square := (7150808484665489517251302221230000000000000)
      linear := (-476528218393742196765396588321766437500000000)
      constant := (7996986477374823575962221390301323829206739806) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree069.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 69 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree069.table
  base := (3085183085959135422645026316274296871189/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1298442)
      previous := (649221)
      next := (649221)
      square := (7150808484665489517251302221230000000000000)
      linear := (-477852868805688928876356478391743000000000000)
      constant := (8041184998505507183796666339217336718522034602) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree069.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 69 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 69 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell045.Kernel069

namespace ForestUnimodality.Stage130KernelData.Cell045.Kernel070
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (206038790936641938389/50000000000000000000)
  centralHi := (412077581873283876779/100000000000000000000)
  directionLo := (415096505616372501323/100000000000000000000)
  directionHi := (103774126404093125331/25000000000000000000)

def endpointA : IntegerEndpointWitness 70 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree070.table
  base := (7079153684852771948490148286575875560427/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 846810000000000000000000000000000000000000000
      center := (11685978)
      previous := (5842989)
      next := (5842989)
      square := (64357276361989405655261719991070000000000000)
      linear := (-4350948030189463991409585211798780125000000000)
      constant := (74137160034196959643253445501150537685129393787) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree070.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 70 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree070.table
  base := (1769787919107632114880012080889800955937/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1298442)
      previous := (649221)
      next := (649221)
      square := (7150808484665489517251302221230000000000000)
      linear := (-484782518265055485728125781575203000000000000)
      constant := (8282951550968622745000351555367078548777644932) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree070.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 70 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 70 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell045.Kernel070

namespace ForestUnimodality.Stage130KernelData.Cell045.Kernel071
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (415096505616372501323/100000000000000000000)
  centralHi := (103774126404093125331/25000000000000000000)
  directionLo := (209046815610351595693/50000000000000000000)
  directionHi := (418093631220703191387/100000000000000000000)

def endpointA : IntegerEndpointWitness 71 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree071.table
  base := (2004421785203055794284365755515467874221/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 846810000000000000000000000000000000000000000
      center := (11685978)
      previous := (5842989)
      next := (5842989)
      square := (64357276361989405655261719991070000000000000)
      linear := (-4413142094835248211930601128701662312500000000)
      constant := (76334012678089303586469100089684276101458102754) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree071.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 71 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree071.table
  base := (801768549796923324749435787230855290629/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1298442)
      previous := (649221)
      next := (649221)
      square := (7150808484665489517251302221230000000000000)
      linear := (-491712167724422042579895084758663000000000000)
      constant := (8528355670548601262837396579878744174295282610) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree071.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 71 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 71 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell045.Kernel071

namespace ForestUnimodality.Stage130KernelData.Cell045.Kernel072
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (209046815610351595693/50000000000000000000)
  centralHi := (418093631220703191387/100000000000000000000)
  directionLo := (105267356039189432209/25000000000000000000)
  directionHi := (421069424156757728837/100000000000000000000)

def endpointA : IntegerEndpointWitness 72 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree072.table
  base := (8985968605528574738798144720098469206657/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1298442)
      previous := (649221)
      next := (649221)
      square := (7150808484665489517251302221230000000000000)
      linear := (-497259573275670270272401893956060500000000000)
      constant := (8729270688344371814511896971278782340515435713) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree072.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 72 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree072.table
  base := (4492983630993746684350972471207710038291/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1298442)
      previous := (649221)
      next := (649221)
      square := (7150808484665489517251302221230000000000000)
      linear := (-498641817183788599431664387942123000000000000)
      constant := (8777397353721331031980433071863322687500560038) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree072.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 72 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 72 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell045.Kernel072

namespace ForestUnimodality.Stage130KernelData.Cell045.Kernel073
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (105267356039189432209/25000000000000000000)
  centralHi := (421069424156757728837/100000000000000000000)
  directionLo := (10600608339032179691/2500000000000000000)
  directionHi := (424024333561287187641/100000000000000000000)

def endpointA : IntegerEndpointWitness 73 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree073.table
  base := (9983997765871360207848347169127822175471/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 846810000000000000000000000000000000000000000
      center := (11685978)
      previous := (5842989)
      next := (5842989)
      square := (64357276361989405655261719991070000000000000)
      linear := (-4537530224126816652972632962507426687500000000)
      constant := (80825430558710886848279110535583902573996528501) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree073.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 73 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree073.table
  base := (4991998333657840247252049439781427115749/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1298442)
      previous := (649221)
      next := (649221)
      square := (7150808484665489517251302221230000000000000)
      linear := (-505571466643155156283433691125583000000000000)
      constant := (9030076597653107019485299402774345895464164682) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree073.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 73 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 73 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell045.Kernel073

namespace ForestUnimodality.Stage130KernelData.Cell045.Kernel074
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (10600608339032179691/2500000000000000000)
  centralHi := (424024333561287187641/100000000000000000000)
  directionLo := (426958793028652743859/100000000000000000000)
  directionHi := (21347939651432637193/5000000000000000000)

def endpointA : IntegerEndpointWitness 74 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree074.table
  base := (11011774369975347924830147604375258971883/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 846810000000000000000000000000000000000000000
      center := (11685978)
      previous := (5842989)
      next := (5842989)
      square := (64357276361989405655261719991070000000000000)
      linear := (-4599724288772600873493648879410308875000000000)
      constant := (83119995747595725457330657114264976678044899323) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree074.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 74 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree074.table
  base := (11011773471902204409551672836861795729463/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1298442)
      previous := (649221)
      next := (649221)
      square := (7150808484665489517251302221230000000000000)
      linear := (-512501116102521713135202994309043000000000000)
      constant := (9286393400066465813015775449929434636018517367) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree074.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 74 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 74 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell045.Kernel074

namespace ForestUnimodality.Stage130KernelData.Cell045.Kernel075
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (426958793028652743859/100000000000000000000)
  centralHi := (21347939651432637193/5000000000000000000)
  directionLo := (107468305338386315351/25000000000000000000)
  directionHi := (85974644270709052281/20000000000000000000)

def endpointA : IntegerEndpointWitness 75 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree075.table
  base := (603464910768206960236764794293813081963/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1298442)
      previous := (649221)
      next := (649221)
      square := (7150808484665489517251302221230000000000000)
      linear := (-517990928157598343779407199590354562500000000)
      constant := (9494125749400884248968503205272214225744266090) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree075.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 75 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree075.table
  base := (6034648740660110549612645545567672325951/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1298442)
      previous := (649221)
      next := (649221)
      square := (7150808484665489517251302221230000000000000)
      linear := (-519430765561888269986972297492503000000000000)
      constant := (9546347759132045237238307507149217457829745918) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree075.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 75 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 75 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell045.Kernel075

namespace ForestUnimodality.Stage130KernelData.Cell045.Kernel076
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (107468305338386315351/25000000000000000000)
  centralHi := (85974644270709052281/20000000000000000000)
  directionLo := (27048001451792861083/6250000000000000000)
  directionHi := (432768023228685777329/100000000000000000000)

def endpointA : IntegerEndpointWitness 76 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree076.table
  base := (526262765574852708996267035559451728821/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 846810000000000000000000000000000000000000000
      center := (11685978)
      previous := (5842989)
      next := (5842989)
      square := (64357276361989405655261719991070000000000000)
      linear := (-4724112418064169314535680713216073250000000000)
      constant := (87806838535972830397817798484587732600894777525) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree076.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 76 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree076.table
  base := (13156568539504027192944589325036686551517/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1298442)
      previous := (649221)
      next := (649221)
      square := (7150808484665489517251302221230000000000000)
      linear := (-526360415021254826838741600675963000000000000)
      constant := (9809939673381423089139104926571778183763223453) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree076.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 76 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 76 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell045.Kernel076

namespace ForestUnimodality.Stage130KernelData.Cell045.Kernel077
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (27048001451792861083/6250000000000000000)
  centralHi := (432768023228685777329/100000000000000000000)
  directionLo := (435643589900797809697/100000000000000000000)
  directionHi := (217821794950398904849/50000000000000000000)

def endpointA : IntegerEndpointWitness 77 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree077.table
  base := (14273587011414931604770149622695258822951/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 846810000000000000000000000000000000000000000
      center := (11685978)
      previous := (5842989)
      next := (5842989)
      square := (64357276361989405655261719991070000000000000)
      linear := (-4786306482709953535056696630118955437500000000)
      constant := (90199116110632531661435567446461664540023032381) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree077.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 77 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree077.table
  base := (2854717304256568183439602974554952490637/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1298442)
      previous := (649221)
      next := (649221)
      square := (7150808484665489517251302221230000000000000)
      linear := (-533290064480621383690510903859423000000000000)
      constant := (10077169141636867483011197509164688739922017665) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree077.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 77 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 77 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell045.Kernel077

namespace ForestUnimodality.Stage130KernelData.Cell045.Kernel078
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (435643589900797809697/100000000000000000000)
  centralHi := (217821794950398904849/50000000000000000000)
  directionLo := (219250149893930913023/50000000000000000000)
  directionHi := (438500299787861826047/100000000000000000000)

def endpointA : IntegerEndpointWitness 78 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree078.table
  base := (15420351726766960371653539311606066441799/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1298442)
      previous := (649221)
      next := (649221)
      square := (7150808484665489517251302221230000000000000)
      linear := (-538722283039526417286412505224648625000000000)
      constant := (10291551606635398725547053671874813633447761791) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree078.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 78 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree078.table
  base := (7710175663181734499172788518805387749417/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1298442)
      previous := (649221)
      next := (649221)
      square := (7150808484665489517251302221230000000000000)
      linear := (-540219713939987940542280207042883000000000000)
      constant := (10348036162954719763342906582462333786668529106) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree078.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 78 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 78 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell045.Kernel078

namespace ForestUnimodality.Stage130KernelData.Cell045.Kernel079
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (219250149893930913023/50000000000000000000)
  centralHi := (438500299787861826047/100000000000000000000)
  directionLo := (220669259530204435903/50000000000000000000)
  directionHi := (441338519060408871807/100000000000000000000)

def endpointA : IntegerEndpointWitness 79 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree079.table
  base := (16596863201528691490135035926765967202249/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 846810000000000000000000000000000000000000000
      center := (11685978)
      previous := (5842989)
      next := (5842989)
      square := (64357276361989405655261719991070000000000000)
      linear := (-4910694612001521976098728463924719812500000000)
      constant := (95081383576126374127069491075441959356446616319) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree079.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 79 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree079.table
  base := (16596862874480915391265412655086903157209/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1298442)
      previous := (649221)
      next := (649221)
      square := (7150808484665489517251302221230000000000000)
      linear := (-547149363399354497394049510226343000000000000)
      constant := (10622540736579766582345680535950329671806179481) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree079.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 79 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 79 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell045.Kernel079

namespace ForestUnimodality.Stage130KernelData.Cell045.Kernel080
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (220669259530204435903/50000000000000000000)
  centralHi := (441338519060408871807/100000000000000000000)
  directionLo := (444158602189381305551/100000000000000000000)
  directionHi := (27759912636836331597/6250000000000000000)

def endpointA : IntegerEndpointWitness 80 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree080.table
  base := (17803121368578813626365979997226706648931/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 846810000000000000000000000000000000000000000
      center := (11685978)
      previous := (5842989)
      next := (5842989)
      square := (64357276361989405655261719991070000000000000)
      linear := (-4972888676647306196619744380827602000000000000)
      constant := (97571373454171988687811953199508205370738126011) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree080.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 80 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree080.table
  base := (17803121101490449547244515244443049785543/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1298442)
      previous := (649221)
      next := (649221)
      square := (7150808484665489517251302221230000000000000)
      linear := (-554079012858721054245818813409803000000000000)
      constant := (10900682861908470170286678691651204655432174087) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree080.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 80 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 80 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell045.Kernel080

namespace ForestUnimodality.Stage130KernelData.Cell045.Kernel081
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (444158602189381305551/100000000000000000000)
  centralHi := (27759912636836331597/6250000000000000000)
  directionLo := (223480446231440608059/50000000000000000000)
  directionHi := (446960892462881216119/100000000000000000000)

def endpointA : IntegerEndpointWitness 81 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree081.table
  base := (19039126174306114439566851830919689218749/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1298442)
      previous := (649221)
      next := (649221)
      square := (7150808484665489517251302221230000000000000)
      linear := (-559453637921454490793417810858942687500000000)
      constant := (11121548232146175682213479879114222222558428091) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree081.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 81 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree081.table
  base := (19039125956218557228884710865347534993191/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1298442)
      previous := (649221)
      next := (649221)
      square := (7150808484665489517251302221230000000000000)
      linear := (-561008662318087611097588116593263000000000000)
      constant := (11182462538459338931706221630960377956750934119) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree081.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 81 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 81 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell045.Kernel081

namespace ForestUnimodality.Stage130KernelData.Cell045.Kernel082
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (223480446231440608059/50000000000000000000)
  centralHi := (446960892462881216119/100000000000000000000)
  directionLo := (44974572247393910877/10000000000000000000)
  directionHi := (449745722473939108771/100000000000000000000)

def endpointA : IntegerEndpointWitness 82 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree082.table
  base := (20304877575975037315300926131364576258227/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 846810000000000000000000000000000000000000000
      center := (11685978)
      previous := (5842989)
      next := (5842989)
      square := (64357276361989405655261719991070000000000000)
      linear := (-5097276805938874637661776214633366375000000000)
      constant := (102649065477938261813730471878170091695794795587) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree082.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 82 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree082.table
  base := (20304877397925591758485994769242080829437/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1298442)
      previous := (649221)
      next := (649221)
      square := (7150808484665489517251302221230000000000000)
      linear := (-567938311777454167949357419776723000000000000)
      constant := (11467879765849053531013830009198664738524172733) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree082.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 82 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 82 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell045.Kernel082

namespace ForestUnimodality.Stage130KernelData.Cell045.Kernel083
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (44974572247393910877/10000000000000000000)
  centralHi := (449745722473939108771/100000000000000000000)
  directionLo := (452513414581264815319/100000000000000000000)
  directionHi := (11312835364531620383/2500000000000000000)

def endpointA : IntegerEndpointWitness 83 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree083.table
  base := (21600375539601688400581305427566578109553/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 846810000000000000000000000000000000000000000
      center := (11685978)
      previous := (5842989)
      next := (5842989)
      square := (64357276361989405655261719991070000000000000)
      linear := (-5159470870584658858182792131536248562500000000)
      constant := (105236767617162240593874628633193170666031776343) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree083.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 83 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree083.table
  base := (10800187697130738796627808041333186566381/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1298442)
      previous := (649221)
      next := (649221)
      square := (7150808484665489517251302221230000000000000)
      linear := (-574867961236820724801126722960183000000000000)
      constant := (11756934543773232107427366833397676904806157658) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree083.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 83 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 83 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell045.Kernel083

namespace ForestUnimodality.Stage130KernelData.Cell045.Kernel084
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (452513414581264815319/100000000000000000000)
  centralHi := (11312835364531620383/2500000000000000000)
  directionLo := (9105285626895750253/2000000000000000000)
  directionHi := (455264281344787512651/100000000000000000000)

def endpointA : IntegerEndpointWitness 84 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree084.table
  base := (22925620038241551336953286605417733220769/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1298442)
      previous := (649221)
      next := (649221)
      square := (7150808484665489517251302221230000000000000)
      linear := (-580184992803382564300423116493236750000000000)
      constant := (11984115611633980987844831829187940069061715521) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree084.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 84 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree084.table
  base := (11462809959809410540869904276907836611231/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1298442)
      previous := (649221)
      next := (649221)
      square := (7150808484665489517251302221230000000000000)
      linear := (-581797610696187281652896026143643000000000000)
      constant := (12049626871990934694080303616894183669350144958) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree084.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 84 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 84 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell045.Kernel084

namespace ForestUnimodality.Stage130KernelData.Cell045.Kernel085
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (9105285626895750253/2000000000000000000)
  centralHi := (455264281344787512651/100000000000000000000)
  directionLo := (457998625937650636137/100000000000000000000)
  directionHi := (228999312968825318069/50000000000000000000)

def endpointA : IntegerEndpointWitness 85 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree085.table
  base := (12140305525304629176027438198504912843529/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 846810000000000000000000000000000000000000000
      center := (11685978)
      previous := (5842989)
      next := (5842989)
      square := (64357276361989405655261719991070000000000000)
      linear := (-5283858999876227299224823965342012937500000000)
      constant := (110509884138766560475585659414745225931329977248) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree085.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 85 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree085.table
  base := (971224438152253089869440144067707073297/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1298442)
      previous := (649221)
      next := (649221)
      square := (7150808484665489517251302221230000000000000)
      linear := (-588727260155553838504665329327103000000000000)
      constant := (12345956750312181396532141391909581396316286825) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree085.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 85 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 85 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell045.Kernel085

namespace ForestUnimodality.Stage130KernelData.Cell045.Kernel086
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (457998625937650636137/100000000000000000000)
  centralHi := (228999312968825318069/50000000000000000000)
  directionLo := (460716742536198939117/100000000000000000000)
  directionHi := (230358371268099469559/50000000000000000000)

def endpointA : IntegerEndpointWitness 86 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree086.table
  base := (802042142498942722885886433184724594867/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 846810000000000000000000000000000000000000000
      center := (11685978)
      previous := (5842989)
      next := (5842989)
      square := (64357276361989405655261719991070000000000000)
      linear := (-5346053064522011519745839882244895125000000000)
      constant := (113195298517926990379068460758569772477420712664) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree086.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 86 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree086.table
  base := (25665348480980370743100519230047114258361/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1298442)
      previous := (649221)
      next := (649221)
      square := (7150808484665489517251302221230000000000000)
      linear := (-595656909614920395356434632510563000000000000)
      constant := (12645924178587899543910423254541151298056918649) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree086.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 86 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 86 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell045.Kernel086

namespace ForestUnimodality.Stage130KernelData.Cell045.Kernel087
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (460716742536198939117/100000000000000000000)
  centralHi := (230358371268099469559/50000000000000000000)
  directionLo := (4634189166893777241/1000000000000000000)
  directionHi := (463418916689377724101/100000000000000000000)

def endpointA : IntegerEndpointWitness 87 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree087.table
  base := (6769958138305979127937726229999291391263/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1298442)
      previous := (649221)
      next := (649221)
      square := (7150808484665489517251302221230000000000000)
      linear := (-600916347685310637807428422127530812500000000)
      constant := (12879253737897642565460758740725562736563293018) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree087.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 87 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree087.table
  base := (27079832488784620518176856085903892224829/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1298442)
      previous := (649221)
      next := (649221)
      square := (7150808484665489517251302221230000000000000)
      linear := (-602586559074286952208203935694023000000000000)
      constant := (12949529156701828417340704202376750721943416061) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree087.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 87 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 87 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell045.Kernel087

namespace ForestUnimodality.Stage130KernelData.Cell045.Kernel088
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (4634189166893777241/1000000000000000000)
  centralHi := (463418916689377724101/100000000000000000000)
  directionLo := (46610542566885724093/10000000000000000000)
  directionHi := (466105425668857240931/100000000000000000000)

def endpointA : IntegerEndpointWitness 88 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree088.table
  base := (14262031510111077971404537320014529632543/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 846810000000000000000000000000000000000000000
      center := (11685978)
      previous := (5842989)
      next := (5842989)
      square := (64357276361989405655261719991070000000000000)
      linear := (-5470441193813579960787871716050659500000000000)
      constant := (118663839507361549961111860170109877861376747566) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree088.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 88 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree088.table
  base := (28524062967657332871846553749566197311741/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1298442)
      previous := (649221)
      next := (649221)
      square := (7150808484665489517251302221230000000000000)
      linear := (-609516208533653509059973238877483000000000000)
      constant := (13256771684564001570348569641327452350506171069) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree088.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 88 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 88 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell045.Kernel088

namespace ForestUnimodality.Stage130KernelData.Cell045.Kernel089
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (46610542566885724093/10000000000000000000)
  centralHi := (466105425668857240931/100000000000000000000)
  directionLo := (93755307760219483667/20000000000000000000)
  directionHi := (14649266837534294323/3125000000000000000)

def endpointA : IntegerEndpointWitness 89 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree089.table
  base := (3749754994143341025913404119871115917343/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 846810000000000000000000000000000000000000000
      center := (11685978)
      previous := (5842989)
      next := (5842989)
      square := (64357276361989405655261719991070000000000000)
      linear := (-5532635258459364181308887632953541687500000000)
      constant := (121446966116113580347567836483769096309702649414) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree089.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 89 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree089.table
  base := (1874877494392109963236152675923836997547/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1298442)
      previous := (649221)
      next := (649221)
      square := (7150808484665489517251302221230000000000000)
      linear := (-616445857993020065911742542060943000000000000)
      constant := (13567651762105500445310575598449825116958715568) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree089.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 89 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 89 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell045.Kernel089

namespace ForestUnimodality.Stage130KernelData.Cell045.Kernel090
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (93755307760219483667/20000000000000000000)
  centralHi := (14649266837534294323/3125000000000000000)
  directionLo := (471432517782478581763/100000000000000000000)
  directionHi := (117858129445619645441/25000000000000000000)

def endpointA : IntegerEndpointWitness 90 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree090.table
  base := (15750881673030553188985325203287352614191/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1298442)
      previous := (649221)
      next := (649221)
      square := (7150808484665489517251302221230000000000000)
      linear := (-621647702567238711314433727761824875000000000)
      constant := (13806962607425795912420689582359794633915721238) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree090.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 90 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree090.table
  base := (31501763311097429894404742041602416417009/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1298442)
      previous := (649221)
      next := (649221)
      square := (7150808484665489517251302221230000000000000)
      linear := (-623375507452386622763511845244403000000000000)
      constant := (13882169389274232393704992820057207136067637681) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree090.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 90 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 90 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell045.Kernel090

namespace ForestUnimodality.Stage130KernelData.Cell045.Kernel091
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (471432517782478581763/100000000000000000000)
  centralHi := (117858129445619645441/25000000000000000000)
  directionLo := (474073616978541820061/100000000000000000000)
  directionHi := (237036808489270910031/50000000000000000000)

def endpointA : IntegerEndpointWitness 91 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree091.table
  base := (8258808298632286695018256608097848627357/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 846810000000000000000000000000000000000000000
      center := (11685978)
      previous := (5842989)
      next := (5842989)
      square := (64357276361989405655261719991070000000000000)
      linear := (-5657023387750932622350919466759306062500000000)
      constant := (127110931559141641471247471585603964326402091218) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree091.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 91 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree091.table
  base := (165176165830095797202634183329189193693/50000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1298442)
      previous := (649221)
      next := (649221)
      square := (7150808484665489517251302221230000000000000)
      linear := (-630305156911753179615281148427863000000000000)
      constant := (14200324566031534095003441539833321224691487400) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree091.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 91 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 91 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell045.Kernel091

namespace ForestUnimodality.Stage130KernelData.Cell045.Kernel092
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (474073616978541820061/100000000000000000000)
  centralHi := (237036808489270910031/50000000000000000000)
  directionLo := (238350041854153743863/50000000000000000000)
  directionHi := (476700083708307487727/100000000000000000000)

def endpointA : IntegerEndpointWitness 92 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree092.table
  base := (6919689899062292668482037109295223001839/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 846810000000000000000000000000000000000000000
      center := (11685978)
      previous := (5842989)
      next := (5842989)
      square := (64357276361989405655261719991070000000000000)
      linear := (-5719217452396716842871935383662188250000000000)
      constant := (129991770392767700674055991732202681137281141795) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree092.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 92 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree092.table
  base := (8649612368016683094540277273677662371603/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1298442)
      previous := (649221)
      next := (649221)
      square := (7150808484665489517251302221230000000000000)
      linear := (-637234806371119736467050451611323000000000000)
      constant := (14522117292349439971948227899847728501017650508) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree092.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 92 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 92 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell045.Kernel092

namespace ForestUnimodality.Stage130KernelData.Cell045.Kernel093
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (238350041854153743863/50000000000000000000)
  centralHi := (476700083708307487727/100000000000000000000)
  directionLo := (479312158514571333331/100000000000000000000)
  directionHi := (119828039628642833333/25000000000000000000)

def endpointA : IntegerEndpointWitness 93 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree093.table
  base := (18095706123060575941469228400796899088571/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1298442)
      previous := (649221)
      next := (649221)
      square := (7150808484665489517251302221230000000000000)
      linear := (-642379057449166784821439033396118937500000000)
      constant := (14767242218612964831908014064616832144216697828) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree093.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 93 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree093.table
  base := (18095706113585761133868311461728729240959/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1298442)
      previous := (649221)
      next := (649221)
      square := (7150808484665489517251302221230000000000000)
      linear := (-644164455830486293318819754794783000000000000)
      constant := (14847547568208486318369428959468010226856366462) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree093.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 93 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 93 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell045.Kernel093

namespace ForestUnimodality.Stage130KernelData.Cell045.Kernel094
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (479312158514571333331/100000000000000000000)
  centralHi := (119828039628642833333/25000000000000000000)
  directionLo := (96382015084202871743/20000000000000000000)
  directionHi := (120477518855253589679/25000000000000000000)

def endpointA : IntegerEndpointWitness 94 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree094.table
  base := (4726765180678419269158519305961301449871/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 846810000000000000000000000000000000000000000
      center := (11685978)
      previous := (5842989)
      next := (5842989)
      square := (64357276361989405655261719991070000000000000)
      linear := (-5843605581688285283913967217467952625000000000)
      constant := (135851160283258955303263989154650063289534084208) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree094.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 94 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree094.table
  base := (37814121429980973704731138012539291312583/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1298442)
      previous := (649221)
      next := (649221)
      square := (7150808484665489517251302221230000000000000)
      linear := (-651094105289852850170589057978243000000000000)
      constant := (15176615393595946940465894961221244191960093447) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree094.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 94 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 94 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell045.Kernel094

namespace ForestUnimodality.Stage130KernelData.Cell045.Kernel095
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (96382015084202871743/20000000000000000000)
  centralHi := (120477518855253589679/25000000000000000000)
  directionLo := (242247031088452113139/50000000000000000000)
  directionHi := (484494062176904226279/100000000000000000000)

def endpointA : IntegerEndpointWitness 95 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree095.table
  base := (9866644273074344704468237848994356350479/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 846810000000000000000000000000000000000000000
      center := (11685978)
      previous := (5842989)
      next := (5842989)
      square := (64357276361989405655261719991070000000000000)
      linear := (-5905799646334069504434983134370834812500000000)
      constant := (138829711339915534887347874547292701613877617546) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree095.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 95 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree095.table
  base := (19733288539854010291095261411177722966527/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1298442)
      previous := (649221)
      next := (649221)
      square := (7150808484665489517251302221230000000000000)
      linear := (-658023754749219407022358361161703000000000000)
      constant := (15509320768504416333237294481451327390784105086) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree095.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 95 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 95 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell045.Kernel095

namespace ForestUnimodality.Stage130KernelData.Cell045.Kernel096
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (242247031088452113139/50000000000000000000)
  centralHi := (484494062176904226279/100000000000000000000)
  directionLo := (487064340490112383277/100000000000000000000)
  directionHi := (243532170245056191639/50000000000000000000)

def endpointA : IntegerEndpointWitness 96 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree096.table
  base := (41148779186269893185763086526446394591059/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1298442)
      previous := (649221)
      next := (649221)
      square := (7150808484665489517251302221230000000000000)
      linear := (-663110412331094858328444339030413000000000000)
      constant := (15760092570827484013979786533119552126707274131) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree096.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 96 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree096.table
  base := (20574389588005123922335745808349252238189/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1298442)
      previous := (649221)
      next := (649221)
      square := (7150808484665489517251302221230000000000000)
      linear := (-664953404208585963874127664345163000000000000)
      constant := (15845663692930672713426961644666284228618240602) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree096.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 96 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 96 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell045.Kernel096

namespace ForestUnimodality.Stage130KernelData.Cell045.Kernel097
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (487064340490112383277/100000000000000000000)
  centralHi := (243532170245056191639/50000000000000000000)
  directionLo := (1912582524410631439/390625000000000000)
  directionHi := (97924225249824329677/20000000000000000000)

def endpointA : IntegerEndpointWitness 97 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree097.table
  base := (42860727727253148710110502626271304245097/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (1242)
      previous := (621)
      next := (621)
      square := (6839969854606164911814403230000000000000)
      linear := (-640895714276292692685409179315187500000000)
      constant := (15398504163656780705705245530254070156174623) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree097.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 97 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree097.table
  base := (10715181929723250041282789722737964592149/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (138)
      previous := (69)
      next := (69)
      square := (759996650511796101312711470000000000000)
      linear := (-71408550713992190533095649647000000000000)
      constant := (1720230010295968367420847055069951858368596) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree097.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 97 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 97 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell045.Kernel097

namespace ForestUnimodality.Stage130KernelData.Cell045.Kernel098
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (1912582524410631439/390625000000000000)
  centralHi := (97924225249824329677/20000000000000000000)
  directionLo := (246082314867326716881/50000000000000000000)
  directionHi := (492164629734653433763/100000000000000000000)

def endpointA : IntegerEndpointWitness 98 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree098.table
  base := (22301211357721686097614155421301925136743/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 846810000000000000000000000000000000000000000
      center := (11685978)
      previous := (5842989)
      next := (5842989)
      square := (64357276361989405655261719991070000000000000)
      linear := (-6092381840271422165998030885079481375000000000)
      constant := (147960788955130032171851642300598385252430942966) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree098.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 98 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree098.table
  base := (5575302838578970819531340385810254028119/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1298442)
      previous := (649221)
      next := (649221)
      square := (7150808484665489517251302221230000000000000)
      linear := (-678812703127319077577666270712083000000000000)
      constant := (16529262190339289376264976767046823441204573368) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree098.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 98 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 98 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell045.Kernel098

namespace ForestUnimodality.Stage130KernelData.Cell045.Kernel099
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (246082314867326716881/50000000000000000000)
  centralHi := (492164629734653433763/100000000000000000000)
  directionLo := (494695055821501718913/100000000000000000000)
  directionHi := (247347527910750859457/50000000000000000000)

def endpointA : IntegerEndpointWitness 99 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree099.table
  base := (23186932075629698743241952294234526864447/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1298442)
      previous := (649221)
      next := (649221)
      square := (7150808484665489517251302221230000000000000)
      linear := (-683841767213022931835449644664707062500000000)
      constant := (16785513663925885658921177373221984267453132396) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 99 interval.damping) (curvature.centralUpper 99 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree099.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 99 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree099.table
  base := (46373864145710077192023391363773496982253/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1298442)
      previous := (649221)
      next := (649221)
      square := (7150808484665489517251302221230000000000000)
      linear := (-685742352586685634429435573895543000000000000)
      constant := (16876517763328791270440744208520221833106018477) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 99 interval.damping) (curvature.centralUpper 99 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree099.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 99 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 99 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell045.Kernel099

namespace ForestUnimodality.Stage130KernelData.Cell045.Kernel100
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (494695055821501718913/100000000000000000000)
  centralHi := (247347527910750859457/50000000000000000000)
  directionLo := (99442520834224409267/20000000000000000000)
  directionHi := (3884473470086890987/781250000000000000)

def endpointA : IntegerEndpointWitness 100 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree100.table
  base := (9635010407058074575754693465523506021019/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 846810000000000000000000000000000000000000000
      center := (11685978)
      previous := (5842989)
      next := (5842989)
      square := (64357276361989405655261719991070000000000000)
      linear := (-6216769969562990607040062718885245750000000000)
      constant := (154211027736505355602057621081252831434017049695) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 100 interval.damping) (curvature.centralUpper 100 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree100.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 100 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree100.table
  base := (12043763007692469997726700071220166535287/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1298442)
      previous := (649221)
      next := (649221)
      square := (7150808484665489517251302221230000000000000)
      linear := (-692672002046052191281204877079003000000000000)
      constant := (17227410885849312139554820167985742187722061532) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 100 interval.damping) (curvature.centralUpper 100 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree100.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 100 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 100 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell045.Kernel100

namespace ForestUnimodality.Stage130KernelData.Cell045.Kernel101
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (99442520834224409267/20000000000000000000)
  centralHi := (3884473470086890987/781250000000000000)
  directionLo := (499717469415487898633/100000000000000000000)
  directionHi := (249858734707743949317/50000000000000000000)

def endpointA : IntegerEndpointWitness 101 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree101.table
  base := (10001197273650798564976940852716429793821/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 846810000000000000000000000000000000000000000
      center := (11685978)
      previous := (5842989)
      next := (5842989)
      square := (64357276361989405655261719991070000000000000)
      linear := (-6278964034208774827561078635788127937500000000)
      constant := (157385003238707961271109232131703671261051999255) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 101 interval.damping) (curvature.centralUpper 101 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree101.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 101 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree101.table
  base := (25002993182285976960140716105502247950237/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1298442)
      previous := (649221)
      next := (649221)
      square := (7150808484665489517251302221230000000000000)
      linear := (-699601651505418748132974180262463000000000000)
      constant := (17581941557908010152911287603979924301927559866) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 101 interval.damping) (curvature.centralUpper 101 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree101.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 101 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 101 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell045.Kernel101

namespace ForestUnimodality.Stage130KernelData.Cell045.Kernel102
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (499717469415487898633/100000000000000000000)
  centralHi := (249858734707743949317/50000000000000000000)
  directionLo := (502209841332693593221/100000000000000000000)
  directionHi := (251104920666346796611/50000000000000000000)

def endpointA : IntegerEndpointWitness 102 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree102.table
  base := (51866667150963197201684496676212857683929/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1298442)
      previous := (649221)
      next := (649221)
      square := (7150808484665489517251302221230000000000000)
      linear := (-704573122094951005342454950299001125000000000)
      constant := (17843505498001069833239821542667705697869962961) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 102 interval.damping) (curvature.centralUpper 102 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree102.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 102 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree102.table
  base := (51866667147964391030686977967988295056101/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1298442)
      previous := (649221)
      next := (649221)
      square := (7150808484665489517251302221230000000000000)
      linear := (-706531300964785304984743483445923000000000000)
      constant := (17940109779512865008613674467483127868182854309) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 102 interval.damping) (curvature.centralUpper 102 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree102.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 102 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 102 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell045.Kernel102

namespace ForestUnimodality.Stage130KernelData.Cell045.Kernel103
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (502209841332693593221/100000000000000000000)
  centralHi := (251104920666346796611/50000000000000000000)
  directionLo := (504689905014752068451/100000000000000000000)
  directionHi := (126172476253688017113/25000000000000000000)

def endpointA : IntegerEndpointWitness 103 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree103.table
  base := (1679909199509365010810620788670129340429/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 846810000000000000000000000000000000000000000
      center := (11685978)
      previous := (5842989)
      next := (5842989)
      square := (64357276361989405655261719991070000000000000)
      linear := (-6403352163500343268603110469593892312500000000)
      constant := (163830666466485020044336874415689955418140249518) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 103 interval.damping) (curvature.centralUpper 103 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree103.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 103 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree103.table
  base := (26878547190928781046121300277139609689979/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1298442)
      previous := (649221)
      next := (649221)
      square := (7150808484665489517251302221230000000000000)
      linear := (-713460950424151861836512786629383000000000000)
      constant := (18301915550672442385238031963147742175146024822) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 103 interval.damping) (curvature.centralUpper 103 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree103.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 103 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 103 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell045.Kernel103

namespace ForestUnimodality.Stage130KernelData.Cell045.Kernel104
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (504689905014752068451/100000000000000000000)
  centralHi := (126172476253688017113/25000000000000000000)
  directionLo := (50715784102800742943/10000000000000000000)
  directionHi := (507157841028007429431/100000000000000000000)

def endpointA : IntegerEndpointWitness 104 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree104.table
  base := (55677268069192873813086282630696865641821/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 846810000000000000000000000000000000000000000
      center := (11685978)
      previous := (5842989)
      next := (5842989)
      square := (64357276361989405655261719991070000000000000)
      linear := (-6465546228146127489124126386496774500000000000)
      constant := (167102354192212841100190504989050246623165044101) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 104 interval.damping) (curvature.centralUpper 104 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree104.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 104 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree104.table
  base := (2783863403360214463045890435272170834691/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1298442)
      previous := (649221)
      next := (649221)
      square := (7150808484665489517251302221230000000000000)
      linear := (-720390599883518418688282089812843000000000000)
      constant := (18667358871395707386449877198666709107672152380) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 104 interval.damping) (curvature.centralUpper 104 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree104.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 104 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 104 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell045.Kernel104

namespace ForestUnimodality.Stage130KernelData.Cell045.Kernel105
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (50715784102800742943/10000000000000000000)
  centralHi := (507157841028007429431/100000000000000000000)
  directionLo := (509613825566555686943/100000000000000000000)
  directionHi := (15925432048954865217/3125000000000000000)

def endpointA : IntegerEndpointWitness 105 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree105.table
  base := (57627188206603326273266875368794835388629/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1298442)
      previous := (649221)
      next := (649221)
      square := (7150808484665489517251302221230000000000000)
      linear := (-725304476976879078849460255933295187500000000)
      constant := (18934068073252714654295075077813628543183329011) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 105 interval.damping) (curvature.centralUpper 105 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree105.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 105 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree105.table
  base := (57627188204984197859510545967389219423911/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1298442)
      previous := (649221)
      next := (649221)
      square := (7150808484665489517251302221230000000000000)
      linear := (-727320249342884975540051392996303000000000000)
      constant := (19036439741691877306911416024863480165559578599) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 105 interval.damping) (curvature.centralUpper 105 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree105.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 105 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 105 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell045.Kernel105

namespace ForestUnimodality.Stage130KernelData.Cell045.Kernel106
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (509613825566555686943/100000000000000000000)
  centralHi := (15925432048954865217/3125000000000000000)
  directionLo := (512058030599042590147/100000000000000000000)
  directionHi := (128014507649760647537/25000000000000000000)

def endpointA : IntegerEndpointWitness 106 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree106.table
  base := (3725428424844350824036240424562223634189/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 846810000000000000000000000000000000000000000
      center := (11685978)
      previous := (5842989)
      next := (5842989)
      square := (64357276361989405655261719991070000000000000)
      linear := (-6589934357437695930166158220302538875000000000)
      constant := (173743441867752659158099600506648215113615014344) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 106 interval.damping) (curvature.centralUpper 106 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree106.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 106 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree106.table
  base := (5960685479619141973414729864350293171649/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1298442)
      previous := (649221)
      next := (649221)
      square := (7150808484665489517251302221230000000000000)
      linear := (-734249898802251532391820696179763000000000000)
      constant := (19409158161570305933162852551366617084520454410) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 106 interval.damping) (curvature.centralUpper 106 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree106.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 106 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 106 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell045.Kernel106

namespace ForestUnimodality.Stage130KernelData.Cell045.Kernel107
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (512058030599042590147/100000000000000000000)
  centralHi := (128014507649760647537/25000000000000000000)
  directionLo := (51449062400918466921/10000000000000000000)
  directionHi := (514490624009184669211/100000000000000000000)

def endpointA : IntegerEndpointWitness 107 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree107.table
  base := (61616267842898077590048224969389029327731/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 846810000000000000000000000000000000000000000
      center := (11685978)
      previous := (5842989)
      next := (5842989)
      square := (64357276361989405655261719991070000000000000)
      linear := (-6652128422083480150687174137205421062500000000)
      constant := (177112841817731047423748512447691483118575807561) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 107 interval.damping) (curvature.centralUpper 107 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree107.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 107 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree107.table
  base := (7702033480228122763309354412794761389731/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1298442)
      previous := (649221)
      next := (649221)
      square := (7150808484665489517251302221230000000000000)
      linear := (-741179548261618089243589999363223000000000000)
      constant := (19785514131040393112332661223637828279327831832) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 107 interval.damping) (curvature.centralUpper 107 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree107.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 107 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 107 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell045.Kernel107

namespace ForestUnimodality.Stage130KernelData.Cell045.Kernel108
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (51449062400918466921/10000000000000000000)
  centralHi := (514490624009184669211/100000000000000000000)
  directionLo := (51691176973033842811/10000000000000000000)
  directionHi := (516911769730338428111/100000000000000000000)

def endpointA : IntegerEndpointWitness 108 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree108.table
  base := (31827713671877419705072696169588067920053/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1298442)
      previous := (649221)
      next := (649221)
      square := (7150808484665489517251302221230000000000000)
      linear := (-746035831858807152356465561567589250000000000)
      constant := (20057201389921455811843113113550644254307057354) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 108 interval.damping) (curvature.centralUpper 108 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree108.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 108 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree108.table
  base := (63655427342881345933462905035026248839799/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1298442)
      previous := (649221)
      next := (649221)
      square := (7150808484665489517251302221230000000000000)
      linear := (-748109197720984646095359302546683000000000000)
      constant := (20165507650111514545564970410875005975333668791) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 108 interval.damping) (curvature.centralUpper 108 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree108.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 108 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 108 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell045.Kernel108

namespace ForestUnimodality.Stage130KernelData.Cell045.Kernel109
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (51691176973033842811/10000000000000000000)
  centralHi := (516911769730338428111/100000000000000000000)
  directionLo := (259660813937211466397/50000000000000000000)
  directionHi := (103864325574884586559/20000000000000000000)

def endpointA : IntegerEndpointWitness 109 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree109.table
  base := (16431083325264905067280650588003883076437/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 846810000000000000000000000000000000000000000
      center := (11685978)
      previous := (5842989)
      next := (5842989)
      square := (64357276361989405655261719991070000000000000)
      linear := (-6776516551375048591729205971011185437500000000)
      constant := (183949353942521787613481337622811703462569765138) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 109 interval.damping) (curvature.centralUpper 109 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree109.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 109 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree109.table
  base := (32862166650174331298104573831755343492247/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1298442)
      previous := (649221)
      next := (649221)
      square := (7150808484665489517251302221230000000000000)
      linear := (-755038847180351202947128605730143000000000000)
      constant := (20549138718792967749204527806163379053837104046) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 109 interval.damping) (curvature.centralUpper 109 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree109.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 109 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 109 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell045.Kernel109

namespace ForestUnimodality.Stage130KernelData.Cell045.Kernel110
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (259660813937211466397/50000000000000000000)
  centralHi := (103864325574884586559/20000000000000000000)
  directionLo := (52172035485548270957/10000000000000000000)
  directionHi := (521720354855482709571/100000000000000000000)

def endpointA : IntegerEndpointWitness 110 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree110.table
  base := (33911492857890509650382969260406577965259/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 846810000000000000000000000000000000000000000
      center := (11685978)
      previous := (5842989)
      next := (5842989)
      square := (64357276361989405655261719991070000000000000)
      linear := (-6838710616020832812250221887914067625000000000)
      constant := (187416466117499125287676610588215586308524069758) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 110 interval.damping) (curvature.centralUpper 110 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree110.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 110 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree110.table
  base := (33911492857601201085861859071836592677869/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1298442)
      previous := (649221)
      next := (649221)
      square := (7150808484665489517251302221230000000000000)
      linear := (-761968496639717759798897908913603000000000000)
      constant := (20936407337093930921205921957482651001012138842) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 110 interval.damping) (curvature.centralUpper 110 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree110.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 110 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 110 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell045.Kernel110

namespace ForestUnimodality.Stage130KernelData.Cell045.Kernel111
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (52172035485548270957/10000000000000000000)
  centralHi := (521720354855482709571/100000000000000000000)
  directionLo := (524108103508160796803/100000000000000000000)
  directionHi := (131027025877040199201/25000000000000000000)

def endpointA : IntegerEndpointWitness 111 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree111.table
  base := (34975692294436473320643090171998977640341/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1298442)
      previous := (649221)
      next := (649221)
      square := (7150808484665489517251302221230000000000000)
      linear := (-766767186740735225863470867201883312500000000)
      constant := (21212905448256210377046477992985989846685155688) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 111 interval.damping) (curvature.centralUpper 111 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree111.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 111 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree111.table
  base := (69951384588402074551567277817244048550013/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1298442)
      previous := (649221)
      next := (649221)
      square := (7150808484665489517251302221230000000000000)
      linear := (-768898146099084316650667212097063000000000000)
      constant := (21327313505023432090138847127397162252807072317) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 111 interval.damping) (curvature.centralUpper 111 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree111.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 111 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 111 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell045.Kernel111

namespace ForestUnimodality.Stage130KernelData.Cell045.Kernel112
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (524108103508160796803/100000000000000000000)
  centralHi := (131027025877040199201/25000000000000000000)
  directionLo := (263242511600667941277/50000000000000000000)
  directionHi := (105297004640267176511/20000000000000000000)

def endpointA : IntegerEndpointWitness 112 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree112.table
  base := (36054764960635989376018744039541141142297/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 846810000000000000000000000000000000000000000
      center := (11685978)
      previous := (5842989)
      next := (5842989)
      square := (64357276361989405655261719991070000000000000)
      linear := (-6963098745312401253292253721719832000000000000)
      constant := (194448402693021402162030343313553073871141704514) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 112 interval.damping) (curvature.centralUpper 112 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree112.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 112 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree112.table
  base := (72109529920888819445820941735952377259401/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1298442)
      previous := (649221)
      next := (649221)
      square := (7150808484665489517251302221230000000000000)
      linear := (-775827795558450873502436515280523000000000000)
      constant := (21721857222590326439535456527428631917633704009) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 112 interval.damping) (curvature.centralUpper 112 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree112.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 112 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 112 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell045.Kernel112

namespace ForestUnimodality.Stage130KernelData.Cell045.Kernel113
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (263242511600667941277/50000000000000000000)
  centralHi := (105297004640267176511/20000000000000000000)
  directionLo := (528851259947162623179/100000000000000000000)
  directionHi := (26442562997358131159/5000000000000000000)

def endpointA : IntegerEndpointWitness 113 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree113.table
  base := (37148710856947722999589581652393920457727/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 846810000000000000000000000000000000000000000
      center := (11685978)
      previous := (5842989)
      next := (5842989)
      square := (64357276361989405655261719991070000000000000)
      linear := (-7025292809958185473813269638622714187500000000)
      constant := (198013227093723332046249470535240814675604528924) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 113 interval.damping) (curvature.centralUpper 113 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree113.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 113 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree113.table
  base := (2321794428549490169357452053430703798511/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1298442)
      previous := (649221)
      next := (649221)
      square := (7150808484665489517251302221230000000000000)
      linear := (-782757445017817430354205818463983000000000000)
      constant := (22120038489803280115343400045993202745286079968) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 113 interval.damping) (curvature.centralUpper 113 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree113.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 113 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 113 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell045.Kernel113

namespace ForestUnimodality.Stage130KernelData.Cell045.Kernel114
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (528851259947162623179/100000000000000000000)
  centralHi := (26442562997358131159/5000000000000000000)
  directionLo := (531206956505740391667/100000000000000000000)
  directionHi := (132801739126435097917/25000000000000000000)

def endpointA : IntegerEndpointWitness 114 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree114.table
  base := (76515059967640100210100448878956051997029/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1298442)
      previous := (649221)
      next := (649221)
      square := (7150808484665489517251302221230000000000000)
      linear := (-787498541622663299370476172836177375000000000)
      constant := (22401180248498624543063425786264666710036920861) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 114 interval.damping) (curvature.centralUpper 114 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree114.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 114 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree114.table
  base := (76515059967386453621527048653387208270107/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1298442)
      previous := (649221)
      next := (649221)
      square := (7150808484665489517251302221230000000000000)
      linear := (-789687094477183987205975121647443000000000000)
      constant := (22521857306670759158394627317678842242613436763) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 114 interval.damping) (curvature.centralUpper 114 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree114.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 114 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 114 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell045.Kernel114

namespace ForestUnimodality.Stage130KernelData.Cell045.Kernel115
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (531206956505740391667/100000000000000000000)
  centralHi := (132801739126435097917/25000000000000000000)
  directionLo := (10671045049712455507/2000000000000000000)
  directionHi := (533552252485622775351/100000000000000000000)

def endpointA : IntegerEndpointWitness 115 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree115.table
  base := (78762444683381239968715409498551306740487/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 846810000000000000000000000000000000000000000
      center := (11685978)
      previous := (5842989)
      next := (5842989)
      square := (64357276361989405655261719991070000000000000)
      linear := (-7149680939249753914855301472428478562500000000)
      constant := (205240588121388389845378854849580272627477898397) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 115 interval.damping) (curvature.centralUpper 115 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree115.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 115 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree115.table
  base := (19690611170793722613947443894353261939463/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1298442)
      previous := (649221)
      next := (649221)
      square := (7150808484665489517251302221230000000000000)
      linear := (-796616743936550544057744424830903000000000000)
      constant := (22927313673201022472781580669350724366353629468) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 115 interval.damping) (curvature.centralUpper 115 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree115.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 115 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 115 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell045.Kernel115

namespace ForestUnimodality.Stage130KernelData.Cell045.Kernel116
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (10671045049712455507/2000000000000000000)
  centralHi := (533552252485622775351/100000000000000000000)
  directionLo := (267943642220184031133/50000000000000000000)
  directionHi := (535887284440368062267/100000000000000000000)

def endpointA : IntegerEndpointWitness 116 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree116.table
  base := (20259893965493048902016336485847959795169/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 846810000000000000000000000000000000000000000
      center := (11685978)
      previous := (5842989)
      next := (5842989)
      square := (64357276361989405655261719991070000000000000)
      linear := (-7211875003895538135376317389331360750000000000)
      constant := (208903124748497899785605809246171419263346324356) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 116 interval.damping) (curvature.centralUpper 116 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree116.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 116 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree116.table
  base := (40519787930902168223848718438955956979847/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1298442)
      previous := (649221)
      next := (649221)
      square := (7150808484665489517251302221230000000000000)
      linear := (-803546393395917100909513728014363000000000000)
      constant := (23336407589402117957508414767845301198446760846) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 116 interval.damping) (curvature.centralUpper 116 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree116.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 116 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 116 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell045.Kernel116

namespace ForestUnimodality.Stage130KernelData.Cell045.Kernel117
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (267943642220184031133/50000000000000000000)
  centralHi := (535887284440368062267/100000000000000000000)
  directionLo := (134553046490329915329/25000000000000000000)
  directionHi := (538212185961319661317/100000000000000000000)

def endpointA : IntegerEndpointWitness 117 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree117.table
  base := (1666929070084881906835936451328751017943/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1298442)
      previous := (649221)
      next := (649221)
      square := (7150808484665489517251302221230000000000000)
      linear := (-808229896504591372877481478470471437500000000)
      constant := (23622025790876281275167944442458715302621753100) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 117 interval.damping) (curvature.centralUpper 117 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree117.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 117 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree117.table
  base := (83346453504107557075372950747103434145823/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1298442)
      previous := (649221)
      next := (649221)
      square := (7150808484665489517251302221230000000000000)
      linear := (-810476042855283657761283031197823000000000000)
      constant := (23749139055281881102958788150433167211878048607) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 117 interval.damping) (curvature.centralUpper 117 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree117.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 117 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 117 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell045.Kernel117

namespace ForestUnimodality.Stage130KernelData.Cell045.Kernel118
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (134553046490329915329/25000000000000000000)
  centralHi := (538212185961319661317/100000000000000000000)
  directionLo := (540527087766794835917/100000000000000000000)
  directionHi := (270263543883397417959/50000000000000000000)

def endpointA : IntegerEndpointWitness 118 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree118.table
  base := (85683077611005849659603658644316722374959/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 846810000000000000000000000000000000000000000
      center := (11685978)
      previous := (5842989)
      next := (5842989)
      square := (64357276361989405655261719991070000000000000)
      linear := (-7336263133187106576418349223137125125000000000)
      constant := (216325910229622784267273689367615487427980778079) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 118 interval.damping) (curvature.centralUpper 118 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree118.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 118 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree118.table
  base := (4284153880544739811034475261354827463791/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1298442)
      previous := (649221)
      next := (649221)
      square := (7150808484665489517251302221230000000000000)
      linear := (-817405692314650214613052334381283000000000000)
      constant := (24165508070847935493817245643402525432136190380) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 118 interval.damping) (curvature.centralUpper 118 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree118.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 118 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 118 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell045.Kernel118

namespace ForestUnimodality.Stage130KernelData.Cell045.Kernel119
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (540527087766794835917/100000000000000000000)
  centralHi := (270263543883397417959/50000000000000000000)
  directionLo := (27141605889392512067/5000000000000000000)
  directionHi := (542832117787850241341/100000000000000000000)

def endpointA : IntegerEndpointWitness 119 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree119.table
  base := (88049448183044303732433730007963312841949/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 846810000000000000000000000000000000000000000
      center := (11685978)
      previous := (5842989)
      next := (5842989)
      square := (64357276361989405655261719991070000000000000)
      linear := (-7398457197832890796939365140040007312500000000)
      constant := (220086159083773288993813414475871886977874552019) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 119 interval.damping) (curvature.centralUpper 119 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree119.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 119 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree119.table
  base := (88049448182953984869115650218172174223557/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1298442)
      previous := (649221)
      next := (649221)
      square := (7150808484665489517251302221230000000000000)
      linear := (-824335341774016771464821637564743000000000000)
      constant := (24585514636107694772726060832765118987269447813) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 119 interval.damping) (curvature.centralUpper 119 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree119.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 119 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 119 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell045.Kernel119

namespace ForestUnimodality.Stage130KernelData.Cell045.Kernel120
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (27141605889392512067/5000000000000000000)
  centralHi := (542832117787850241341/100000000000000000000)
  directionLo := (545127401250783493603/100000000000000000000)
  directionHi := (136281850312695873401/25000000000000000000)

def endpointA : IntegerEndpointWitness 120 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree120.table
  base := (90445565221124517725369497484138674489631/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1298442)
      previous := (649221)
      next := (649221)
      square := (7150808484665489517251302221230000000000000)
      linear := (-828961251386519446384486784104765500000000000)
      constant := (24875442075600314635107780352463179382022938079) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 120 interval.damping) (curvature.centralUpper 120 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree120.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 120 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree120.table
  base := (18089113044210213461816117626063763104431/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1298442)
      previous := (649221)
      next := (649221)
      square := (7150808484665489517251302221230000000000000)
      linear := (-831264991233383328316590940748203000000000000)
      constant := (25009158751068365709495064083996529735247956395) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 120 interval.damping) (curvature.centralUpper 120 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree120.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 120 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 120 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell045.Kernel120

namespace ForestUnimodality.Stage130KernelData.Cell045.Kernel121
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (545127401250783493603/100000000000000000000)
  centralHi := (136281850312695873401/25000000000000000000)
  directionLo := (273706530378260659093/50000000000000000000)
  directionHi := (547413060756521318187/100000000000000000000)

def endpointA : IntegerEndpointWitness 121 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree121.table
  base := (92871428725990143078776654417667050997947/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 846810000000000000000000000000000000000000000
      center := (11685978)
      previous := (5842989)
      next := (5842989)
      square := (64357276361989405655261719991070000000000000)
      linear := (-7522845327124459237981396973845771687500000000)
      constant := (227704369019574385581365122734638731588037618657) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 121 interval.damping) (curvature.centralUpper 121 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree121.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 121 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree121.table
  base := (92871428725930414811570918550993787419613/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1298442)
      previous := (649221)
      next := (649221)
      square := (7150808484665489517251302221230000000000000)
      linear := (-838194640692749885168360243931663000000000000)
      constant := (25436440415736952093412968312615143545831138717) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 121 interval.damping) (curvature.centralUpper 121 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree121.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 121 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 121 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell045.Kernel121

namespace ForestUnimodality.Stage130KernelData.Cell045.Kernel122
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (273706530378260659093/50000000000000000000)
  centralHi := (547413060756521318187/100000000000000000000)
  directionLo := (549689216357036688497/100000000000000000000)
  directionHi := (274844608178518344249/50000000000000000000)

def endpointA : IntegerEndpointWitness 122 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree122.table
  base := (23831759674590967344496322235814324637071/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 846810000000000000000000000000000000000000000
      center := (11685978)
      previous := (5842989)
      next := (5842989)
      square := (64357276361989405655261719991070000000000000)
      linear := (-7585039391770243458502412890748653875000000000)
      constant := (231562330101349148666774050356617519077664112404) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 122 interval.damping) (curvature.centralUpper 122 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree122.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 122 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree122.table
  base := (95327038698315302976967456025452272408753/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1298442)
      previous := (649221)
      next := (649221)
      square := (7150808484665489517251302221230000000000000)
      linear := (-845124290152116442020129547115123000000000000)
      constant := (25867359630120259224603756602677266431093956977) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 122 interval.damping) (curvature.centralUpper 122 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree122.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 122 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 122 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell045.Kernel122

namespace ForestUnimodality.Stage130KernelData.Cell045.Kernel123
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (549689216357036688497/100000000000000000000)
  centralHi := (274844608178518344249/50000000000000000000)
  directionLo := (551955985628929729181/100000000000000000000)
  directionHi := (275977992814464864591/50000000000000000000)

def endpointA : IntegerEndpointWitness 123 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree123.table
  base := (48906197569473960849999508360218831926363/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1298442)
      previous := (649221)
      next := (649221)
      square := (7150808484665489517251302221230000000000000)
      linear := (-849692606268447519891492089739059562500000000)
      constant := (26161429102865176232660283246196609818545767684) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 123 interval.damping) (curvature.centralUpper 123 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree123.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 123 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree123.table
  base := (9781239513890843391584934042719346423703/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1298442)
      previous := (649221)
      next := (649221)
      square := (7150808484665489517251302221230000000000000)
      linear := (-852053939611482998871898850298583000000000000)
      constant := (26301916394224898827225868081252652305006215270) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 123 interval.damping) (curvature.centralUpper 123 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree123.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 123 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 123 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell045.Kernel123

namespace ForestUnimodality.Stage130KernelData.Cell045.Kernel124
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (551955985628929729181/100000000000000000000)
  centralHi := (275977992814464864591/50000000000000000000)
  directionLo := (22168539349771999719/4000000000000000000)
  directionHi := (34638342734018749561/6250000000000000000)

def endpointA : IntegerEndpointWitness 124 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree124.table
  base := (100327498048424592553742010296949111288723/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 846810000000000000000000000000000000000000000
      center := (11685978)
      previous := (5842989)
      next := (5842989)
      square := (64357276361989405655261719991070000000000000)
      linear := (-7709427521061811899544444724554418250000000000)
      constant := (239375964492944475074818827167609892060227852363) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 124 interval.damping) (curvature.centralUpper 124 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree124.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 124 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree124.table
  base := (20065499609678497684597065172741093433721/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1298442)
      previous := (649221)
      next := (649221)
      square := (7150808484665489517251302221230000000000000)
      linear := (-858983589070849555723668153482043000000000000)
      constant := (26740110708057294244877281955738656740589404445) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 124 interval.damping) (curvature.centralUpper 124 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree124.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 124 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 124 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell045.Kernel124

namespace ForestUnimodality.Stage130KernelData.Cell045.Kernel125
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (22168539349771999719/4000000000000000000)
  centralHi := (34638342734018749561/6250000000000000000)
  directionLo := (556461823539030989467/100000000000000000000)
  directionHi := (139115455884757747367/25000000000000000000)

def endpointA : IntegerEndpointWitness 125 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree125.table
  base := (25718086856864198980173907831122144825891/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 846810000000000000000000000000000000000000000
      center := (11685978)
      previous := (5842989)
      next := (5842989)
      square := (64357276361989405655261719991070000000000000)
      linear := (-7771621585707596120065460641457300437500000000)
      constant := (243331637802878951828268707398166078602266821834) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 125 interval.damping) (curvature.centralUpper 125 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree125.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 125 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree125.table
  base := (102872347427430696501838178269814142617833/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1298442)
      previous := (649221)
      next := (649221)
      square := (7150808484665489517251302221230000000000000)
      linear := (-865913238530216112575437456665503000000000000)
      constant := (27181942571623685808660579390816056267891190697) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 125 interval.damping) (curvature.centralUpper 125 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree125.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 125 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 125 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell045.Kernel125

namespace ForestUnimodality.Stage130KernelData.Cell045.Kernel126
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (556461823539030989467/100000000000000000000)
  centralHi := (139115455884757747367/25000000000000000000)
  directionLo := (558701115578601520147/100000000000000000000)
  directionHi := (139675278894650380037/25000000000000000000)

def endpointA : IntegerEndpointWitness 126 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree126.table
  base := (13180867909586079202341218460075422903201/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1298442)
      previous := (649221)
      next := (649221)
      square := (7150808484665489517251302221230000000000000)
      linear := (-870423961150375593398497395373353625000000000)
      constant := (27479986872849395504481247576575181355816620672) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 126 interval.damping) (curvature.centralUpper 126 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree126.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 126 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree126.table
  base := (21089388655333483431195754327987616382809/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1298442)
      previous := (649221)
      next := (649221)
      square := (7150808484665489517251302221230000000000000)
      linear := (-872842887989582669427206759848963000000000000)
      constant := (27627411984930136292440358739898335412729249405) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 126 interval.damping) (curvature.centralUpper 126 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree126.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 126 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 126 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell045.Kernel126

namespace ForestUnimodality.Stage130KernelData.Cell045.Kernel127
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (558701115578601520147/100000000000000000000)
  centralHi := (139675278894650380037/25000000000000000000)
  directionLo := (560931468221532428819/100000000000000000000)
  directionHi := (28046573411076621441/5000000000000000000)

def endpointA : IntegerEndpointWitness 127 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree127.table
  base := (108051285596745966385121059957170674295097/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 846810000000000000000000000000000000000000000
      center := (11685978)
      previous := (5842989)
      next := (5842989)
      square := (64357276361989405655261719991070000000000000)
      linear := (-7896009714999164561107492475263064812500000000)
      constant := (251340696651294296724099717823462301904651077807) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 127 interval.damping) (curvature.centralUpper 127 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree127.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 127 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree127.table
  base := (108051285596728720408980294970630195903149/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1298442)
      previous := (649221)
      next := (649221)
      square := (7150808484665489517251302221230000000000000)
      linear := (-879772537448949226278976063032423000000000000)
      constant := (28076518947982536389068420138254060513252728941) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 127 interval.damping) (curvature.centralUpper 127 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree127.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 127 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 127 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell045.Kernel127

namespace ForestUnimodality.Stage130KernelData.Cell045.Kernel128
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (560931468221532428819/100000000000000000000)
  centralHi := (28046573411076621441/5000000000000000000)
  directionLo := (35197061730035736521/6250000000000000000)
  directionHi := (563152987680571784337/100000000000000000000)

def endpointA : IntegerEndpointWitness 128 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree128.table
  base := (27671343597059245952814898117587130084873/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 846810000000000000000000000000000000000000000
      center := (11685978)
      previous := (5842989)
      next := (5842989)
      square := (64357276361989405655261719991070000000000000)
      linear := (-7958203779644948781628508392165947000000000000)
      constant := (255394082189879665482362674950139669050868522052) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 128 interval.damping) (curvature.centralUpper 128 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree128.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 128 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree128.table
  base := (110685374388222966146429438320580531801899/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1298442)
      previous := (649221)
      next := (649221)
      square := (7150808484665489517251302221230000000000000)
      linear := (-886702186908315783130745366215883000000000000)
      constant := (28529263460786610156708248752645446223724067691) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 128 interval.damping) (curvature.centralUpper 128 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree128.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 128 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 128 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell045.Kernel128

namespace ForestUnimodality.Stage130KernelData.Cell045.Kernel129
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (35197061730035736521/6250000000000000000)
  centralHi := (563152987680571784337/100000000000000000000)
  directionLo := (282682889040858125093/50000000000000000000)
  directionHi := (565365778081716250187/100000000000000000000)

def endpointA : IntegerEndpointWitness 129 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree129.table
  base := (28337302412938192161717880663126360683803/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1298442)
      previous := (649221)
      next := (649221)
      square := (7150808484665489517251302221230000000000000)
      linear := (-891155316032303666905502701007647687500000000)
      constant := (28831115385716746588161073555595459155519828458) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 129 interval.damping) (curvature.centralUpper 129 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree129.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 129 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree129.table
  base := (113349209651741375673818333693399680662403/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1298442)
      previous := (649221)
      next := (649221)
      square := (7150808484665489517251302221230000000000000)
      linear := (-893631836367682339982514669399343000000000000)
      constant := (28985645523347920396623220053094464595352549827) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 129 interval.damping) (curvature.centralUpper 129 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree129.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 129 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 129 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell045.Kernel129

namespace ForestUnimodality.Stage130KernelData.Cell045.Kernel130
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (282682889040858125093/50000000000000000000)
  centralHi := (565365778081716250187/100000000000000000000)
  directionLo := (283784970760580720347/50000000000000000000)
  directionHi := (113513988304232288139/20000000000000000000)

def endpointA : IntegerEndpointWitness 130 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree130.table
  base := (7252674461741740755913989688423752497471/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 846810000000000000000000000000000000000000000
      center := (11685978)
      previous := (5842989)
      next := (5842989)
      square := (64357276361989405655261719991070000000000000)
      linear := (-8082591908936517222670540225971711375000000000)
      constant := (263598565496056110034133721889508419608735343016) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 130 interval.damping) (curvature.centralUpper 130 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree130.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 130 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree130.table
  base := (116042791387858592917624373664191331550457/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1298442)
      previous := (649221)
      next := (649221)
      square := (7150808484665489517251302221230000000000000)
      linear := (-900561485827048896834283972582803000000000000)
      constant := (29445665135671873933517559826340266238558249913) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 130 interval.damping) (curvature.centralUpper 130 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree130.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 130 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 130 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell045.Kernel130

namespace ForestUnimodality.Stage130KernelData.Cell045.Kernel131
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (283784970760580720347/50000000000000000000)
  centralHi := (113513988304232288139/20000000000000000000)
  directionLo := (35610348632516837279/6250000000000000000)
  directionHi := (113953115624053879293/20000000000000000000)

def endpointA : IntegerEndpointWitness 131 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree131.table
  base := (118766119597140757592226974227728045423139/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 846810000000000000000000000000000000000000000
      center := (11685978)
      previous := (5842989)
      next := (5842989)
      square := (64357276361989405655261719991070000000000000)
      linear := (-8144785973582301443191556142874593562500000000)
      constant := (267749663263743134027643612782734860738988552409) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 131 interval.damping) (curvature.centralUpper 131 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree131.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 131 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree131.table
  base := (118766119597133233016459771214471639930347/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1298442)
      previous := (649221)
      next := (649221)
      square := (7150808484665489517251302221230000000000000)
      linear := (-907491135286415453686053275766263000000000000)
      constant := (29909322297763726777230470384325936660104634923) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 131 interval.damping) (curvature.centralUpper 131 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree131.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 131 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 131 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell045.Kernel131

namespace ForestUnimodality.Stage130KernelData.Cell045.Kernel132
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (35610348632516837279/6250000000000000000)
  centralHi := (113953115624053879293/20000000000000000000)
  directionLo := (114390557215727382649/20000000000000000000)
  directionHi := (285976393039318456623/50000000000000000000)

def endpointA : IntegerEndpointWitness 132 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree132.table
  base := (121519194280114531273323933398420811080233/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1298442)
      previous := (649221)
      next := (649221)
      square := (7150808484665489517251302221230000000000000)
      linear := (-911886670914231740412508006641941750000000000)
      constant := (30214814641617530773735817442148707216141412297) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 132 interval.damping) (curvature.centralUpper 132 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree132.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 132 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree132.table
  base := (121519194280108416697128545938396695469237/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1298442)
      previous := (649221)
      next := (649221)
      square := (7150808484665489517251302221230000000000000)
      linear := (-914420784745782010537822578949723000000000000)
      constant := (30376617009628589150680450747412890507670050933) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 132 interval.damping) (curvature.centralUpper 132 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree132.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 132 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 132 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell045.Kernel132

namespace ForestUnimodality.Stage130KernelData.Cell045.Kernel133
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (114390557215727382649/20000000000000000000)
  centralHi := (285976393039318456623/50000000000000000000)
  directionLo := (287065830862672155673/50000000000000000000)
  directionHi := (574131661725344311347/100000000000000000000)

def endpointA : IntegerEndpointWitness 133 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree133.table
  base := (124302015437317257846552482173420551241933/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 846810000000000000000000000000000000000000000
      center := (11685978)
      previous := (5842989)
      next := (5842989)
      square := (64357276361989405655261719991070000000000000)
      linear := (-8269174102873869884233587976680357937500000000)
      constant := (276149571028544757583282109450759467097667347123) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 133 interval.damping) (curvature.centralUpper 133 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree133.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 133 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree133.table
  base := (62151007718656144670422123284594995574109/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1298442)
      previous := (649221)
      next := (649221)
      square := (7150808484665489517251302221230000000000000)
      linear := (-921350434205148567389591882133183000000000000)
      constant := (30847549271271430373759339195632027626713583162) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 133 interval.damping) (curvature.centralUpper 133 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree133.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 133 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 133 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell045.Kernel133

namespace ForestUnimodality.Stage130KernelData.Cell045.Kernel134
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (287065830862672155673/50000000000000000000)
  centralHi := (574131661725344311347/100000000000000000000)
  directionLo := (144075574892115080209/25000000000000000000)
  directionHi := (576302299568460320837/100000000000000000000)

def endpointA : IntegerEndpointWitness 134 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree134.table
  base := (5084583322770502442527192555830703890547/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 846810000000000000000000000000000000000000000
      center := (11685978)
      previous := (5842989)
      next := (5842989)
      square := (64357276361989405655261719991070000000000000)
      linear := (-8331368167519654104754603893583240125000000000)
      constant := (280398381025747570059503927396480165495682137675) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 134 interval.damping) (curvature.centralUpper 134 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree134.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 134 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree134.table
  base := (5084583322770340961806133978530645400829/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1298442)
      previous := (649221)
      next := (649221)
      square := (7150808484665489517251302221230000000000000)
      linear := (-928280083664515124241361185316643000000000000)
      constant := (31322119082697083596641950525020853064410001525) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 134 interval.damping) (curvature.centralUpper 134 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree134.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 134 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 134 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell045.Kernel134

namespace ForestUnimodality.Stage130KernelData.Cell045.Kernel135
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (144075574892115080209/25000000000000000000)
  centralHi := (576302299568460320837/100000000000000000000)
  directionLo := (4627718338743000529/800000000000000000)
  directionHi := (289232396171437533063/50000000000000000000)

def endpointA : IntegerEndpointWitness 135 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree135.table
  base := (16244612147056261035121015621421746589729/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1298442)
      previous := (649221)
      next := (649221)
      square := (7150808484665489517251302221230000000000000)
      linear := (-932618025796159813919513312276235812500000000)
      constant := (31631084640689836114465607930038832911938800038) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 135 interval.damping) (curvature.centralUpper 135 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree135.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 135 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree135.table
  base := (129956897176446808299326033752105159616987/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1298442)
      previous := (649221)
      next := (649221)
      square := (7150808484665489517251302221230000000000000)
      linear := (-935209733123881681093130488500103000000000000)
      constant := (31800326443910250378914827851027462446836230683) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 135 interval.damping) (curvature.centralUpper 135 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree135.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 135 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 135 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell045.Kernel135

namespace ForestUnimodality.Stage130KernelData.Cell045.Kernel136
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (4627718338743000529/800000000000000000)
  centralHi := (289232396171437533063/50000000000000000000)
  directionLo := (290309615528264824027/50000000000000000000)
  directionHi := (116123846211305929611/20000000000000000000)

def endpointA : IntegerEndpointWitness 136 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree136.table
  base := (66414478879682989447104715106860430150673/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 846810000000000000000000000000000000000000000
      center := (11685978)
      previous := (5842989)
      next := (5842989)
      square := (64357276361989405655261719991070000000000000)
      linear := (-8455756296811222545796635727389004500000000000)
      constant := (288993713249968789265389783478787859264928280626) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 136 interval.damping) (curvature.centralUpper 136 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree136.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 136 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree136.table
  base := (16603619719920414266605567325701996778557/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1298442)
      previous := (649221)
      next := (649221)
      square := (7150808484665489517251302221230000000000000)
      linear := (-942139382583248237944899791683563000000000000)
      constant := (32282171354915505113203369562001528701515542504) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 136 interval.damping) (curvature.centralUpper 136 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree136.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 136 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 136 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell045.Kernel136

namespace ForestUnimodality.Stage130KernelData.Cell045.Kernel137
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (290309615528264824027/50000000000000000000)
  centralHi := (116123846211305929611/20000000000000000000)
  directionLo := (291382852517553764767/50000000000000000000)
  directionHi := (116553141007021505907/20000000000000000000)

def endpointA : IntegerEndpointWitness 137 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree137.table
  base := (1357307648184833166022681835643341240579/100000000000000000000000000000000000000)
  polynomial :=
    { denominator := 846810000000000000000000000000000000000000000
      center := (11685978)
      previous := (5842989)
      next := (5842989)
      square := (64357276361989405655261719991070000000000000)
      linear := (-8517950361457006766317651644291886687500000000)
      constant := (293340235477068423965847745046017606361202498650) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 137 interval.damping) (curvature.centralUpper 137 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree137.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 137 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree137.table
  base := (135730764818481151782384869912940123069709/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1298442)
      previous := (649221)
      next := (649221)
      square := (7150808484665489517251302221230000000000000)
      linear := (-949069032042614794796669094867023000000000000)
      constant := (32767653815717299293724460197353984617962891981) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 137 interval.damping) (curvature.centralUpper 137 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree137.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 137 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 137 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell045.Kernel137

namespace ForestUnimodality.Stage130KernelData.Cell045.Kernel138
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (291382852517553764767/50000000000000000000)
  centralHi := (116553141007021505907/20000000000000000000)
  directionLo := (584904301965249819819/100000000000000000000)
  directionHi := (29245215098262490991/5000000000000000000)

def endpointA : IntegerEndpointWitness 138 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree138.table
  base := (27732463670852513128726185921511454823367/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1298442)
      previous := (649221)
      next := (649221)
      square := (7150808484665489517251302221230000000000000)
      linear := (-953349380678087887426518617910529875000000000)
      constant := (33079925383060713522638181683776170030837175515) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 138 interval.damping) (curvature.centralUpper 138 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree138.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 138 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree138.table
  base := (17332789794282600882974109965078933324897/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1298442)
      previous := (649221)
      next := (649221)
      square := (7150808484665489517251302221230000000000000)
      linear := (-955998681501981351648438398050483000000000000)
      constant := (33256773826319965631519393378990855469231646984) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 138 interval.damping) (curvature.centralUpper 138 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree138.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 138 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 138 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell045.Kernel138

namespace ForestUnimodality.Stage130KernelData.Cell045.Kernel139
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (584904301965249819819/100000000000000000000)
  centralHi := (29245215098262490991/5000000000000000000)
  directionLo := (117407021587270722327/20000000000000000000)
  directionHi := (146758776984088402909/25000000000000000000)

def endpointA : IntegerEndpointWitness 139 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree139.table
  base := (14162361836715199123913785366674807157713/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 846810000000000000000000000000000000000000000
      center := (11685978)
      previous := (5842989)
      next := (5842989)
      square := (64357276361989405655261719991070000000000000)
      linear := (-8642338490748575207359683478097651062500000000)
      constant := (302130992161440742026243421536058889581547164280) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 139 interval.damping) (curvature.centralUpper 139 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree139.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 139 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree139.table
  base := (70811809183575281370593224882086422526821/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1298442)
      previous := (649221)
      next := (649221)
      square := (7150808484665489517251302221230000000000000)
      linear := (-962928330961347908500207701233943000000000000)
      constant := (33749531386727722019115754256161299299109717578) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 139 interval.damping) (curvature.centralUpper 139 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree139.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 139 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 139 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell045.Kernel139

namespace ForestUnimodality.Stage130KernelData.Cell045.Kernel140
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (117407021587270722327/20000000000000000000)
  centralHi := (146758776984088402909/25000000000000000000)
  directionLo := (589158207481009744019/100000000000000000000)
  directionHi := (29457910374050487201/5000000000000000000)

def endpointA : IntegerEndpointWitness 140 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree140.table
  base := (72307332428794032287297766406129672230069/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 846810000000000000000000000000000000000000000
      center := (11685978)
      previous := (5842989)
      next := (5842989)
      square := (64357276361989405655261719991070000000000000)
      linear := (-8704532555394359427880699395000533250000000000)
      constant := (306575226618788345749832390945132232102916445978) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 140 interval.damping) (curvature.centralUpper 140 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree140.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 140 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree140.table
  base := (72307332428793452131420740044891589096877/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1298442)
      previous := (649221)
      next := (649221)
      square := (7150808484665489517251302221230000000000000)
      linear := (-969857980420714465351977004417403000000000000)
      constant := (34245926496944675348096370772400189923625031386) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 140 interval.damping) (curvature.centralUpper 140 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree140.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 140 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 140 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell045.Kernel140

namespace ForestUnimodality.Stage130KernelData.Cell045.Kernel141
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (589158207481009744019/100000000000000000000)
  centralHi := (29457910374050487201/5000000000000000000)
  directionLo := (295636841807066866089/50000000000000000000)
  directionHi := (591273683614133732179/100000000000000000000)

def endpointA : IntegerEndpointWitness 141 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree141.table
  base := (18454432228249481589453719064305885536873/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1298442)
      previous := (649221)
      next := (649221)
      square := (7150808484665489517251302221230000000000000)
      linear := (-974080735560015960933523923544823937500000000)
      constant := (34561336868847247553188311168957863728924473206) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 141 interval.damping) (curvature.centralUpper 141 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree141.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 141 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree141.table
  base := (147635457825994910288848521842820190781977/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1298442)
      previous := (649221)
      next := (649221)
      square := (7150808484665489517251302221230000000000000)
      linear := (-976787629880081022203746307600863000000000000)
      constant := (34745959156974825183574034923434198175067621593) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 141 interval.damping) (curvature.centralUpper 141 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree141.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 141 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 141 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell045.Kernel141

namespace ForestUnimodality.Stage130KernelData.Cell045.Kernel142
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (295636841807066866089/50000000000000000000)
  centralHi := (591273683614133732179/100000000000000000000)
  directionLo := (296690808935420557447/50000000000000000000)
  directionHi := (118676323574168222979/20000000000000000000)

def endpointA : IntegerEndpointWitness 142 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree142.table
  base := (150685997272789393891472780045200998006729/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 846810000000000000000000000000000000000000000
      center := (11685978)
      previous := (5842989)
      next := (5842989)
      square := (64357276361989405655261719991070000000000000)
      linear := (-8828920684685927868922731228806297625000000000)
      constant := (315561407763986449884120267887375406225879693449) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 142 interval.damping) (curvature.centralUpper 142 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree142.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 142 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree142.table
  base := (150685997272788628473391433075872678852263/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1298442)
      previous := (649221)
      next := (649221)
      square := (7150808484665489517251302221230000000000000)
      linear := (-983717279339447579055515610784323000000000000)
      constant := (35249629366822067299926962629680132035320942567) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 142 interval.damping) (curvature.centralUpper 142 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree142.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 142 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 142 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell045.Kernel142

namespace ForestUnimodality.Stage130KernelData.Cell045.Kernel143
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (296690808935420557447/50000000000000000000)
  centralHi := (118676323574168222979/20000000000000000000)
  directionLo := (595482090343116111423/100000000000000000000)
  directionHi := (9304407661611189241/1562500000000000000)

def endpointA : IntegerEndpointWitness 143 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree143.table
  base := (153766283198372058613429074042525785420841/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 846810000000000000000000000000000000000000000
      center := (11685978)
      previous := (5842989)
      next := (5842989)
      square := (64357276361989405655261719991070000000000000)
      linear := (-8891114749331712089443747145709179812500000000)
      constant := (320103354451906169284376565907321006085515205471) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 143 interval.damping) (curvature.centralUpper 143 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree143.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 143 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree143.table
  base := (76883141599185718494342922983240534665669/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1298442)
      previous := (649221)
      next := (649221)
      square := (7150808484665489517251302221230000000000000)
      linear := (-990646928798814135907284913967783000000000000)
      constant := (35756937126490197082377530774296469381338559242) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 143 interval.damping) (curvature.centralUpper 143 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree143.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 143 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 143 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell045.Kernel143

namespace ForestUnimodality.Stage130KernelData.Cell045.Kernel144
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (595482090343116111423/100000000000000000000)
  centralHi := (9304407661611189241/1562500000000000000)
  directionLo := (298787589857660122847/50000000000000000000)
  directionHi := (119515035943064049139/20000000000000000000)

def endpointA : IntegerEndpointWitness 144 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree144.table
  base := (156876315603136897111258245169504640837489/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1298442)
      previous := (649221)
      next := (649221)
      square := (7150808484665489517251302221230000000000000)
      linear := (-994812090441944034440529229179118000000000000)
      constant := (36075319098157518896218885352335346790639934001) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 144 interval.damping) (curvature.centralUpper 144 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree144.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 144 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree144.table
  base := (78438157801568196145574773949433695031669/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1298442)
      previous := (649221)
      next := (649221)
      square := (7150808484665489517251302221230000000000000)
      linear := (-997576578258180692759054217151243000000000000)
      constant := (36267882435982912799124174318781355273105947242) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 144 interval.damping) (curvature.centralUpper 144 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree144.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 144 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 144 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell045.Kernel144

namespace ForestUnimodality.Stage130KernelData.Cell045.Kernel145
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (298787589857660122847/50000000000000000000)
  centralHi := (119515035943064049139/20000000000000000000)
  directionLo := (14991524082464636959/2500000000000000000)
  directionHi := (599660963298585478361/100000000000000000000)

def endpointA : IntegerEndpointWitness 145 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree145.table
  base := (80008047243733486789618280956153648004953/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 846810000000000000000000000000000000000000000
      center := (11685978)
      previous := (5842989)
      next := (5842989)
      square := (64357276361989405655261719991070000000000000)
      linear := (-9015502878623280530485778979514944187500000000)
      constant := (329284960058553390487935983370144090371207818736) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 145 interval.damping) (curvature.centralUpper 145 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree145.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 145 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree145.table
  base := (160016094487466563635674257005450397730483/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1298442)
      previous := (649221)
      next := (649221)
      square := (7150808484665489517251302221230000000000000)
      linear := (-1004506227717547249610823520334703000000000000)
      constant := (36782465295303818748786169439042717792246114547) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 145 interval.damping) (curvature.centralUpper 145 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree145.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 145 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 145 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell045.Kernel145

namespace ForestUnimodality.Stage130KernelData.Cell045.Kernel146
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (14991524082464636959/2500000000000000000)
  centralHi := (599660963298585478361/100000000000000000000)
  directionLo := (601739517064134380177/100000000000000000000)
  directionHi := (300869758532067190089/50000000000000000000)

def endpointA : IntegerEndpointWitness 146 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree146.table
  base := (1274887655091685060353662141332550547273/78125000000000000000000000000000000000)
  polynomial :=
    { denominator := 846810000000000000000000000000000000000000000
      center := (11685978)
      previous := (5842989)
      next := (5842989)
      square := (64357276361989405655261719991070000000000000)
      linear := (-9077696943269064751006794896417826375000000000)
      constant := (333924618977344950410939691930555232139055863864) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 146 interval.damping) (curvature.centralUpper 146 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree146.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 146 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree146.table
  base := (163185619851735354842852736476582425556781/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1298442)
      previous := (649221)
      next := (649221)
      square := (7150808484665489517251302221230000000000000)
      linear := (-1011435877176913806462592823518163000000000000)
      constant := (37300685704456428287911473443938582042063752429) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 146 interval.damping) (curvature.centralUpper 146 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree146.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 146 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 146 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell045.Kernel146

namespace ForestUnimodality.Stage130KernelData.Cell045.Kernel147
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (601739517064134380177/100000000000000000000)
  centralHi := (300869758532067190089/50000000000000000000)
  directionLo := (150952728918891994169/25000000000000000000)
  directionHi := (603810915675567976677/100000000000000000000)

def endpointA : IntegerEndpointWitness 147 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree147.table
  base := (166384891696307084112761621630456131903997/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1298442)
      previous := (649221)
      next := (649221)
      square := (7150808484665489517251302221230000000000000)
      linear := (-1015543445323872107947534534813412062500000000)
      constant := (37621872071091464165850549452977764920377676523) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 147 interval.damping) (curvature.centralUpper 147 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree147.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 147 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree147.table
  base := (8319244584815340690910848064318098374911/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1298442)
      previous := (649221)
      next := (649221)
      square := (7150808484665489517251302221230000000000000)
      linear := (-1018365526636280363314362126701623000000000000)
      constant := (37822543663444166743243236686000240752190751980) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 147 interval.damping) (curvature.centralUpper 147 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree147.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 147 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 147 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell045.Kernel147

namespace ForestUnimodality.Stage130KernelData.Cell045.Kernel148
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (150952728918891994169/25000000000000000000)
  centralHi := (603810915675567976677/100000000000000000000)
  directionLo := (605875232520160088259/100000000000000000000)
  directionHi := (30293761626008004413/5000000000000000000)

def endpointA : IntegerEndpointWitness 148 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree148.table
  base := (169613910021536149777344227025229791776881/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 846810000000000000000000000000000000000000000
      center := (11685978)
      previous := (5842989)
      next := (5842989)
      square := (64357276361989405655261719991070000000000000)
      linear := (-9202085072560633192048826730223590750000000000)
      constant := (343301649046018132390245847449869247302145559961) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 148 interval.damping) (curvature.centralUpper 148 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree148.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 148 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree148.table
  base := (84806955010767965156587905332920787535097/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1298442)
      previous := (649221)
      next := (649221)
      square := (7150808484665489517251302221230000000000000)
      linear := (-1025295176095646920166131429885083000000000000)
      constant := (38348039172270374213352465309912667379835455346) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 148 interval.damping) (curvature.centralUpper 148 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree148.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 148 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 148 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell045.Kernel148

namespace ForestUnimodality.Stage130KernelData.Cell045.Kernel149
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (605875232520160088259/100000000000000000000)
  centralHi := (30293761626008004413/5000000000000000000)
  directionLo := (607932539739195275959/100000000000000000000)
  directionHi := (15198313493479881899/2500000000000000000)

def endpointA : IntegerEndpointWitness 149 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree149.table
  base := (172872674827769100589960403964099396935501/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 846810000000000000000000000000000000000000000
      center := (11685978)
      previous := (5842989)
      next := (5842989)
      square := (64357276361989405655261719991070000000000000)
      linear := (-9264279137206417412569842647126472937500000000)
      constant := (348039020195959133009879793830399478101719378931) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 149 interval.damping) (curvature.centralUpper 149 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree149.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 149 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree149.table
  base := (172872674827768922405364906690601233570383/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1298442)
      previous := (649221)
      next := (649221)
      square := (7150808484665489517251302221230000000000000)
      linear := (-1032224825555013477017900733068543000000000000)
      constant := (38877172230938308264131632883784994006663733647) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 149 interval.damping) (curvature.centralUpper 149 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree149.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 149 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 149 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell045.Kernel149

namespace ForestUnimodality.Stage130KernelData.Cell045.Kernel150
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (607932539739195275959/100000000000000000000)
  centralHi := (15198313493479881899/2500000000000000000)
  directionLo := (121996581651477175189/20000000000000000000)
  directionHi := (304991454128692937973/50000000000000000000)

def endpointA : IntegerEndpointWitness 150 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree150.table
  base := (88080593057671828412592558202793342922023/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1298442)
      previous := (649221)
      next := (649221)
      square := (7150808484665489517251302221230000000000000)
      linear := (-1036274800205800181454539840447706125000000000)
      constant := (39200995787741641982458674082373572890778503814) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 150 interval.damping) (curvature.centralUpper 150 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree150.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 150 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree150.table
  base := (176161186115343512162293814517119530386363/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1298442)
      previous := (649221)
      next := (649221)
      square := (7150808484665489517251302221230000000000000)
      linear := (-1039154475014380033869670036252003000000000000)
      constant := (39409942839451146522513936906174527661405289467) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 150 interval.damping) (curvature.centralUpper 150 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree150.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 150 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 150 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell045.Kernel150

namespace ForestUnimodality.Stage130KernelData.Cell045.Kernel151
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (121996581651477175189/20000000000000000000)
  centralHi := (304991454128692937973/50000000000000000000)
  directionLo := (1912582524410631439/312500000000000000)
  directionHi := (612026407811402060481/100000000000000000000)

def endpointA : IntegerEndpointWitness 151 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree151.table
  base := (22434930485573663547433804188920355963207/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 846810000000000000000000000000000000000000000
      center := (11685978)
      previous := (5842989)
      next := (5842989)
      square := (64357276361989405655261719991070000000000000)
      linear := (-9388667266497985853611874480932237312500000000)
      constant := (357611474727192968420912123851436759020918124486) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 151 interval.damping) (curvature.centralUpper 151 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree151.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 151 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree151.table
  base := (2804366310696706108392054385448213776429/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1298442)
      previous := (649221)
      next := (649221)
      square := (7150808484665489517251302221230000000000000)
      linear := (-1046084124473746590721439339435463000000000000)
      constant := (39946350997811989172640967634918896579034909504) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 151 interval.damping) (curvature.centralUpper 151 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree151.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 151 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 151 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell045.Kernel151

namespace ForestUnimodality.Stage130KernelData.Cell045.Kernel152
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (1912582524410631439/312500000000000000)
  centralHi := (612026407811402060481/100000000000000000000)
  directionLo := (30703155348877369737/5000000000000000000)
  directionHi := (614063106977547394741/100000000000000000000)

def endpointA : IntegerEndpointWitness 152 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree152.table
  base := (5713357754244611564653562737768630602281/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 846810000000000000000000000000000000000000000
      center := (11685978)
      previous := (5842989)
      next := (5842989)
      square := (64357276361989405655261719991070000000000000)
      linear := (-9450861331143770074132890397835119500000000000)
      constant := (362446558108540930942373930457340225650766235552) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 152 interval.damping) (curvature.centralUpper 152 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree152.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 152 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree152.table
  base := (45706862033956868682318522171883317810213/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1298442)
      previous := (649221)
      next := (649221)
      square := (7150808484665489517251302221230000000000000)
      linear := (-1053013773933113147573208642618923000000000000)
      constant := (40486396706023861358552172840966976549105176468) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 152 interval.damping) (curvature.centralUpper 152 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree152.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 152 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 152 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell045.Kernel152

namespace ForestUnimodality.Stage130KernelData.Cell045.Kernel153
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (30703155348877369737/5000000000000000000)
  centralHi := (614063106977547394741/100000000000000000000)
  directionLo := (77011634149826370441/12500000000000000000)
  directionHi := (616093073198610963529/100000000000000000000)

def endpointA : IntegerEndpointWitness 153 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree153.table
  base := (186205198869372227420456176125657925037887/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1298442)
      previous := (649221)
      next := (649221)
      square := (7150808484665489517251302221230000000000000)
      linear := (-1057006155087728254961545146082000187500000000)
      constant := (40812690248193915230968924585871606806818197533) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 153 interval.damping) (curvature.centralUpper 153 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree153.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 153 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree153.table
  base := (4655129971734303750678779794744235301781/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1298442)
      previous := (649221)
      next := (649221)
      square := (7150808484665489517251302221230000000000000)
      linear := (-1059943423392479704424977945802383000000000000)
      constant := (41030079964089715497316057110529119398178297160) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 153 interval.damping) (curvature.centralUpper 153 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree153.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 153 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 153 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell045.Kernel153

namespace ForestUnimodality.Stage130KernelData.Cell045.Kernel154
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (77011634149826370441/12500000000000000000)
  centralHi := (616093073198610963529/100000000000000000000)
  directionLo := (618116372809925815167/100000000000000000000)
  directionHi := (4829034162577545431/781250000000000000)

def endpointA : IntegerEndpointWitness 154 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree154.table
  base := (189612696085529573354455844491208897763183/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 846810000000000000000000000000000000000000000
      center := (11685978)
      previous := (5842989)
      next := (5842989)
      square := (64357276361989405655261719991070000000000000)
      linear := (-9575249460435338515174922231640883875000000000)
      constant := (372214437102831824020740208768553892138280974623) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 154 interval.damping) (curvature.centralUpper 154 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree154.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 154 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree154.table
  base := (23701587010691188816503034122044759184001/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1298442)
      previous := (649221)
      next := (649221)
      square := (7150808484665489517251302221230000000000000)
      linear := (-1066873072851846261276747248985843000000000000)
      constant := (41577400772012433506368166097161395113298123272) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 154 interval.damping) (curvature.centralUpper 154 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree154.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 154 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 154 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell045.Kernel154

namespace ForestUnimodality.Stage130KernelData.Cell045.Kernel155
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (618116372809925815167/100000000000000000000)
  centralHi := (4829034162577545431/781250000000000000)
  directionLo := (310066535532331104063/50000000000000000000)
  directionHi := (620133071064662208127/100000000000000000000)

def endpointA : IntegerEndpointWitness 155 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree155.table
  base := (24131242473074829517575467943085542880341/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 846810000000000000000000000000000000000000000
      center := (11685978)
      previous := (5842989)
      next := (5842989)
      square := (64357276361989405655261719991070000000000000)
      linear := (-9637443525081122735695938148543766062500000000)
      constant := (377147232715826013781339273722682734313650468518) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 155 interval.damping) (curvature.centralUpper 155 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree155.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 155 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree155.table
  base := (193049939784598585147928837553600704490809/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1298442)
      previous := (649221)
      next := (649221)
      square := (7150808484665489517251302221230000000000000)
      linear := (-1073802722311212818128516552169303000000000000)
      constant := (42128359129794828948666569870290794028554021881) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 155 interval.damping) (curvature.centralUpper 155 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree155.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 155 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 155 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell045.Kernel155

namespace ForestUnimodality.Stage130KernelData.Cell045.Kernel156
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (310066535532331104063/50000000000000000000)
  centralHi := (620133071064662208127/100000000000000000000)
  directionLo := (19441976004949467047/3125000000000000000)
  directionHi := (124428646431676589101/20000000000000000000)

def endpointA : IntegerEndpointWitness 156 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree156.table
  base := (196516929966871398993282188492130731833159/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1298442)
      previous := (649221)
      next := (649221)
      square := (7150808484665489517251302221230000000000000)
      linear := (-1077737509969656328468550451716294250000000000)
      constant := (42456955452528059087899402774354912110505693031) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 156 interval.damping) (curvature.centralUpper 156 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree156.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 156 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree156.table
  base := (6141154061464729925140216071968691282451/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1298442)
      previous := (649221)
      next := (649221)
      square := (7150808484665489517251302221230000000000000)
      linear := (-1080732371770579374980285855352763000000000000)
      constant := (42682955037439649099123282098722457320850606688) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 156 interval.damping) (curvature.centralUpper 156 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree156.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 156 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 156 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell045.Kernel156

namespace ForestUnimodality.Stage130KernelData.Cell045.Kernel157
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (19441976004949467047/3125000000000000000)
  centralHi := (124428646431676589101/20000000000000000000)
  directionLo := (624146919252886940081/100000000000000000000)
  directionHi := (312073459626443470041/50000000000000000000)

def endpointA : IntegerEndpointWitness 157 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree157.table
  base := (50003416658158252914226462880877766953179/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 846810000000000000000000000000000000000000000
      center := (11685978)
      previous := (5842989)
      next := (5842989)
      square := (64357276361989405655261719991070000000000000)
      linear := (-9761831654372691176737969982349530437500000000)
      constant := (387110536173635524815513041363806573295460322346) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 157 interval.damping) (curvature.centralUpper 157 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree157.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 157 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree157.table
  base := (200013666632632978064589900748239639959843/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1298442)
      previous := (649221)
      next := (649221)
      square := (7150808484665489517251302221230000000000000)
      linear := (-1087662021229945931832055158536223000000000000)
      constant := (43241188494949576935620947941756777772382162787) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 157 interval.damping) (curvature.centralUpper 157 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree157.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 157 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 157 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell045.Kernel157

namespace ForestUnimodality.Stage130KernelData.Cell045.Kernel158
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (624146919252886940081/100000000000000000000)
  centralHi := (312073459626443470041/50000000000000000000)
  directionLo := (626144194499366065081/100000000000000000000)
  directionHi := (313072097249683032541/50000000000000000000)

def endpointA : IntegerEndpointWitness 158 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree158.table
  base := (203540149782161994316575889265543940215233/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 846810000000000000000000000000000000000000000
      center := (11685978)
      previous := (5842989)
      next := (5842989)
      square := (64357276361989405655261719991070000000000000)
      linear := (-9824025719018475397258985899252412625000000000)
      constant := (392141044018498578222389073950826984071288020673) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 158 interval.damping) (curvature.centralUpper 158 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree158.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 158 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree158.table
  base := (203540149782161967053207999059718005613883/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1298442)
      previous := (649221)
      next := (649221)
      square := (7150808484665489517251302221230000000000000)
      linear := (-1094591670689312488683824461719683000000000000)
      constant := (43803059502327233057779012031614980714821025147) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 158 interval.damping) (curvature.centralUpper 158 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree158.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 158 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 158 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell045.Kernel158

namespace ForestUnimodality.Stage130KernelData.Cell045.Kernel159
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (626144194499366065081/100000000000000000000)
  centralHi := (313072097249683032541/50000000000000000000)
  directionLo := (628135119060899310059/100000000000000000000)
  directionHi := (31406755953044965503/5000000000000000000)

def endpointA : IntegerEndpointWitness 159 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree159.table
  base := (51774094853932608538654924442152897612051/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1298442)
      previous := (649221)
      next := (649221)
      square := (7150808484665489517251302221230000000000000)
      linear := (-1098468864851584401975555757350588312500000000)
      constant := (44133791400818303625156598772799762211851370186) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 159 interval.damping) (curvature.centralUpper 159 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree159.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 159 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree159.table
  base := (207096379415730412028682244592251494507307/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1298442)
      previous := (649221)
      next := (649221)
      square := (7150808484665489517251302221230000000000000)
      linear := (-1101521320148679045535593764903143000000000000)
      constant := (44368568059575177536493005169950551311819251563) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 159 interval.damping) (curvature.centralUpper 159 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree159.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 159 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 159 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell045.Kernel159

namespace ForestUnimodality.Stage130KernelData.Cell045.Kernel160
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (628135119060899310059/100000000000000000000)
  centralHi := (31406755953044965503/5000000000000000000)
  directionLo := (630119753134307274733/100000000000000000000)
  directionHi := (315059876567153637367/50000000000000000000)

def endpointA : IntegerEndpointWitness 160 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree160.table
  base := (210682355533604174859318329914786180766621/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 846810000000000000000000000000000000000000000
      center := (11685978)
      previous := (5842989)
      next := (5842989)
      square := (64357276361989405655261719991070000000000000)
      linear := (-9948413848310043838301017733058177000000000000)
      constant := (402299771940256499936941314216025953573498232901) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 160 interval.damping) (curvature.centralUpper 160 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree160.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 160 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree160.table
  base := (105341177766802078451719176004383595261061/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1298442)
      previous := (649221)
      next := (649221)
      square := (7150808484665489517251302221230000000000000)
      linear := (-1108450969608045602387363068086603000000000000)
      constant := (44937714166695911697134940906026970495622645898) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 160 interval.damping) (curvature.centralUpper 160 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree160.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 160 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 160 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell045.Kernel160

namespace ForestUnimodality.Stage130KernelData.Cell045.Kernel161
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (630119753134307274733/100000000000000000000)
  centralHi := (315059876567153637367/50000000000000000000)
  directionLo := (126419631194277818683/20000000000000000000)
  directionHi := (79012269496423636677/12500000000000000000)

def endpointA : IntegerEndpointWitness 161 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree161.table
  base := (53574519534010749844593485358756445796973/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 846810000000000000000000000000000000000000000
      center := (11685978)
      previous := (5842989)
      next := (5842989)
      square := (64357276361989405655261719991070000000000000)
      linear := (-10010607912955828058822033649961059187500000000)
      constant := (407427992017195878833779215982764525568301851202) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 161 interval.damping) (curvature.centralUpper 161 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree161.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 161 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree161.table
  base := (107149039068021492403596380845715938274473/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1298442)
      previous := (649221)
      next := (649221)
      square := (7150808484665489517251302221230000000000000)
      linear := (-1115380619067412159239132371270063000000000000)
      constant := (45510497823691879839172321227400045526449032914) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 161 interval.damping) (curvature.centralUpper 161 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree161.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 161 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 161 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell045.Kernel161

namespace ForestUnimodality.Stage130KernelData.Cell045.Kernel162
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (126419631194277818683/20000000000000000000)
  centralHi := (79012269496423636677/12500000000000000000)
  directionLo := (317035192949781493279/50000000000000000000)
  directionHi := (634070385899562986559/100000000000000000000)

def endpointA : IntegerEndpointWitness 162 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree162.table
  base := (217943547223300806196457822857448551780761/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1298442)
      previous := (649221)
      next := (649221)
      square := (7150808484665489517251302221230000000000000)
      linear := (-1119200219733512475482561062984882375000000000)
      constant := (45843198093133818854944838200958349921752055249) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 162 interval.damping) (curvature.centralUpper 162 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree162.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 162 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree162.table
  base := (217943547223300794372412548723896198274667/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1298442)
      previous := (649221)
      next := (649221)
      square := (7150808484665489517251302221230000000000000)
      linear := (-1122310268526778716090901674453523000000000000)
      constant := (46086919030565470894838028843531845329566341803) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 162 interval.damping) (curvature.centralUpper 162 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree162.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 162 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 162 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell045.Kernel162

namespace ForestUnimodality.Stage130KernelData.Cell045.Kernel163
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (317035192949781493279/50000000000000000000)
  centralHi := (634070385899562986559/100000000000000000000)
  directionLo := (31801825017096539073/5000000000000000000)
  directionHi := (636036500341930781461/100000000000000000000)

def endpointA : IntegerEndpointWitness 163 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree163.table
  base := (221618762795625779403512799995746584690203/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 846810000000000000000000000000000000000000000
      center := (11685978)
      previous := (5842989)
      next := (5842989)
      square := (64357276361989405655261719991070000000000000)
      linear := (-10134996042247396499864065483766823562500000000)
      constant := (417782144403302988996034746126337085318912798993) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 163 interval.damping) (curvature.centralUpper 163 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree163.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 163 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree163.table
  base := (221618762795625769809045279261118847289219/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1298442)
      previous := (649221)
      next := (649221)
      square := (7150808484665489517251302221230000000000000)
      linear := (-1129239917986145272942670977636983000000000000)
      constant := (46666977787319020029363460404374376234144261571) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 163 interval.damping) (curvature.centralUpper 163 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree163.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 163 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 163 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell045.Kernel163

namespace ForestUnimodality.Stage130KernelData.Cell045.Kernel164
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (31801825017096539073/5000000000000000000)
  centralHi := (636036500341930781461/100000000000000000000)
  directionLo := (79749569479598241151/12500000000000000000)
  directionHi := (637996555836785929209/100000000000000000000)

def endpointA : IntegerEndpointWitness 164 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree164.table
  base := (4506474497065211056167225954344359098049/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 846810000000000000000000000000000000000000000
      center := (11685978)
      previous := (5842989)
      next := (5842989)
      square := (64357276361989405655261719991070000000000000)
      linear := (-10197190106893180720385081400669705750000000000)
      constant := (423008076712512283211937714696088001756281868450) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 164 interval.damping) (curvature.centralUpper 164 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree164.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 164 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree164.table
  base := (225323724853260545023348337810990151318991/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1298442)
      previous := (649221)
      next := (649221)
      square := (7150808484665489517251302221230000000000000)
      linear := (-1136169567445511829794440280820443000000000000)
      constant := (47250674093954810185172591640762378333760386319) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 164 interval.damping) (curvature.centralUpper 164 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree164.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 164 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 164 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell045.Kernel164

namespace ForestUnimodality.Stage130KernelData.Cell045.Kernel165
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (79749569479598241151/12500000000000000000)
  centralHi := (637996555836785929209/100000000000000000000)
  directionLo := (319975304028291883717/50000000000000000000)
  directionHi := (127990121611316753487/20000000000000000000)

def endpointA : IntegerEndpointWitness 165 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree165.table
  base := (229058433396442368340585579762798138413873/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1298442)
      previous := (649221)
      next := (649221)
      square := (7150808484665489517251302221230000000000000)
      linear := (-1139931574615440548989566368619176437500000000)
      constant := (47585175529539149136227933910413783961191599807) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 165 interval.damping) (curvature.centralUpper 165 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree165.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 165 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree165.table
  base := (57264608349110590506002593309290510923113/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1298442)
      previous := (649221)
      next := (649221)
      square := (7150808484665489517251302221230000000000000)
      linear := (-1143099216904878386646209584003903000000000000)
      constant := (47838007950475073572325174049853952669102280868) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 165 interval.damping) (curvature.centralUpper 165 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree165.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 165 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 165 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell045.Kernel165

namespace ForestUnimodality.Stage130KernelData.Cell045.Kernel166
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (319975304028291883717/50000000000000000000)
  centralHi := (127990121611316753487/20000000000000000000)
  directionLo := (320949355913196018203/50000000000000000000)
  directionHi := (641898711826392036407/100000000000000000000)

def endpointA : IntegerEndpointWitness 166 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree166.table
  base := (232822888425403228972588596822350884477489/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 846810000000000000000000000000000000000000000
      center := (11685978)
      previous := (5842989)
      next := (5842989)
      square := (64357276361989405655261719991070000000000000)
      linear := (-10321578236184749161427113234475470125000000000)
      constant := (433557653563342812282081871886613599152735121009) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 166 interval.damping) (curvature.centralUpper 166 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree166.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 166 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree166.table
  base := (29102861053175402980957134950437390656191/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1298442)
      previous := (649221)
      next := (649221)
      square := (7150808484665489517251302221230000000000000)
      linear := (-1150028866364244943497978887187363000000000000)
      constant := (48428979356881993107392818787096001269472808952) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 166 interval.damping) (curvature.centralUpper 166 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree166.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 166 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 166 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell045.Kernel166

namespace ForestUnimodality.Stage130KernelData.Cell045.Kernel167
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (320949355913196018203/50000000000000000000)
  centralHi := (641898711826392036407/100000000000000000000)
  directionLo := (40240057571364934229/6250000000000000000)
  directionHi := (128768184228367789533/20000000000000000000)

def endpointA : IntegerEndpointWitness 167 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree167.table
  base := (59154272485092511595799572499339884001307/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 846810000000000000000000000000000000000000000
      center := (11685978)
      previous := (5842989)
      next := (5842989)
      square := (64357276361989405655261719991070000000000000)
      linear := (-10383772300830533381948129151378352312500000000)
      constant := (438881298105002908487903943655171343223439181018) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 167 interval.damping) (curvature.centralUpper 167 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree167.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 167 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree167.table
  base := (59154272485092510556313378638737541412851/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1298442)
      previous := (649221)
      next := (649221)
      square := (7150808484665489517251302221230000000000000)
      linear := (-1156958515823611500349748190370823000000000000)
      constant := (49023588313177703802852176079869847108614060236) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 167 interval.damping) (curvature.centralUpper 167 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree167.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 167 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 167 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell045.Kernel167

namespace ForestUnimodality.Stage130KernelData.Cell045.Kernel168
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (40240057571364934229/6250000000000000000)
  centralHi := (128768184228367789533/20000000000000000000)
  directionLo := (64577728918657542803/10000000000000000000)
  directionHi := (645777289186575428031/100000000000000000000)

def endpointA : IntegerEndpointWitness 168 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree168.table
  base := (120220518970782391787064390068948340495151/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1298442)
      previous := (649221)
      next := (649221)
      square := (7150808484665489517251302221230000000000000)
      linear := (-1160662929497368622496571674253470500000000000)
      constant := (49359723710094602988051752663011364965187751518) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 168 interval.damping) (curvature.centralUpper 168 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree168.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 168 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree168.table
  base := (240441037941564780200837755328329234819113/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1298442)
      previous := (649221)
      next := (649221)
      square := (7150808484665489517251302221230000000000000)
      linear := (-1163888165282978057201517493554283000000000000)
      constant := (49621834819364294108984600196896673770413034217) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 168 interval.damping) (curvature.centralUpper 168 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree168.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 168 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 168 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell045.Kernel168

namespace ForestUnimodality.Stage130KernelData.Cell045.Kernel169
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (64577728918657542803/10000000000000000000)
  centralHi := (645777289186575428031/100000000000000000000)
  directionLo := (647707868349267515739/100000000000000000000)
  directionHi := (32385393417463375787/5000000000000000000)

def endpointA : IntegerEndpointWitness 169 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree169.table
  base := (48858946485840918528208133716378819785423/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 846810000000000000000000000000000000000000000
      center := (11685978)
      previous := (5842989)
      next := (5842989)
      square := (64357276361989405655261719991070000000000000)
      linear := (-10508160430122101822990160985184116687500000000)
      constant := (449626299420906756152379998204303824561852494065) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 169 interval.damping) (curvature.centralUpper 169 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree169.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 169 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree169.table
  base := (6107368310730114747610668496366645995031/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1298442)
      previous := (649221)
      next := (649221)
      square := (7150808484665489517251302221230000000000000)
      linear := (-1170817814742344614053286796737743000000000000)
      constant := (50223718875443807210181420507169537886689867160) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 169 interval.damping) (curvature.centralUpper 169 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree169.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 169 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 169 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell045.Kernel169
