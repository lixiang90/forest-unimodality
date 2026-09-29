import ForestUnimodality.FiniteKernelSequentialResidual
import ForestUnimodality.Stage99KernelData.Cell107.Parameters
import ForestUnimodality.BinomialMassData.Q22647_43472.Batch000_049
import ForestUnimodality.BinomialMassData.Q22647_43472.Batch050_099
import ForestUnimodality.BinomialMassData.Q22647_43472.Batch100_149
import ForestUnimodality.BinomialMassData.Q109_209.Batch000_049
import ForestUnimodality.BinomialMassData.Q109_209.Batch050_099
import ForestUnimodality.BinomialMassData.Q109_209.Batch100_149

namespace ForestUnimodality.Stage99KernelData.Cell107.Kernel000
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 0 where
  qNumerator := 22647
  qDenominator := 43472
  table := BinomialMassData.Q22647_43472.Degree000.table
  base := (95194611098201850180378081/1562500000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (122)
      previous := (61)
      next := (61)
      square := (789686672812743017946246480000000000000)
      linear := (-35097701304625536847248135000000000000)
      constant := (609245511028491841154419718400000000000000) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22647_43472.Degree000.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 0 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree000.table
  base := (95194611098201850180378081/1562500000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (122)
      previous := (61)
      next := (61)
      square := (789686672812743017946246480000000000000)
      linear := (-35097701304625536847248135000000000000)
      constant := (609245511028491841154419718400000000000000) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree000.checked
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
end ForestUnimodality.Stage99KernelData.Cell107.Kernel000

namespace ForestUnimodality.Stage99KernelData.Cell107.Kernel001
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 1 where
  qNumerator := 22647
  qDenominator := 43472
  table := BinomialMassData.Q22647_43472.Degree001.table
  base := (332556354969155164008561805513024824703667/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (900614858)
      previous := (450307429)
      next := (450307429)
      square := (5829537300817549292607788731296720000000000000)
      linear := (-6332959428871130486332118367212205000000000000)
      constant := (2456677694941568935078302224798377103296868420363) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22647_43472.Degree001.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 1 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree001.table
  base := (166125855262291137109130397676892197040829/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (5329082)
      previous := (2664541)
      next := (2664541)
      square := (34494303555133427766909992492880000000000000)
      linear := (-37512806877381545458691527906695000000000000)
      constant := (14523268795517387194278986316040971117880903098) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree001.checked
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
end ForestUnimodality.Stage99KernelData.Cell107.Kernel001

namespace ForestUnimodality.Stage99KernelData.Cell107.Kernel002
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (49953619659859091769/100000000000000000000)
  directionHi := (4995361965985909177/10000000000000000000)

def endpointA : IntegerEndpointWitness 2 where
  qNumerator := 22647
  qDenominator := 43472
  table := BinomialMassData.Q22647_43472.Degree002.table
  base := (96010843076656846408241673658529920434057/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (900614858)
      previous := (450307429)
      next := (450307429)
      square := (5829537300817549292607788731296720000000000000)
      linear := (-12406824503016099147985071596770395000000000000)
      constant := (1424119563762046315174186388580750920489254810146) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22647_43472.Degree002.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 2 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree002.table
  base := (95856559255665293883898818805095883806529/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (5329082)
      previous := (2664541)
      next := (2664541)
      square := (34494303555133427766909992492880000000000000)
      linear := (-73492511064075742842358410028455000000000000)
      constant := (8413348920599025552179880345693176601105986498) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree002.checked
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
end ForestUnimodality.Stage99KernelData.Cell107.Kernel002

namespace ForestUnimodality.Stage99KernelData.Cell107.Kernel003
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (49953619659859091769/100000000000000000000)
  centralHi := (4995361965985909177/10000000000000000000)
  directionLo := (70645086412600002753/100000000000000000000)
  directionHi := (35322543206300001377/50000000000000000000)

def endpointA : IntegerEndpointWitness 3 where
  qNumerator := 22647
  qDenominator := 43472
  table := BinomialMassData.Q22647_43472.Degree003.table
  base := (23766529532250700709134690743735532644473/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (900614858)
      previous := (450307429)
      next := (450307429)
      square := (5829537300817549292607788731296720000000000000)
      linear := (-18480689577161067809638024826328585000000000000)
      constant := (891877085954646405716207311791959778469525220485) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22647_43472.Degree003.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 3 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree003.table
  base := (23718550427784525643175338444593183730237/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (5329082)
      previous := (2664541)
      next := (2664541)
      square := (34494303555133427766909992492880000000000000)
      linear := (-109472215250769940226025292150215000000000000)
      constant := (5267089094617735144328435462141599292602411985) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree003.checked
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
end ForestUnimodality.Stage99KernelData.Cell107.Kernel003

namespace ForestUnimodality.Stage99KernelData.Cell107.Kernel004
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (70645086412600002753/100000000000000000000)
  centralHi := (35322543206300001377/50000000000000000000)
  directionLo := (86522207272847485359/100000000000000000000)
  directionHi := (1081527590910593567/1250000000000000000)

def endpointA : IntegerEndpointWitness 4 where
  qNumerator := 22647
  qDenominator := 43472
  table := BinomialMassData.Q22647_43472.Degree004.table
  base := (79221971707352494744280998507751435466043/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (900614858)
      previous := (450307429)
      next := (450307429)
      square := (5829537300817549292607788731296720000000000000)
      linear := (-24554554651306036471290978055886775000000000000)
      constant := (610677285439073933419770765998614522738085903827) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22647_43472.Degree004.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 4 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree004.table
  base := (7905020386890901353033019098528813133957/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (5329082)
      previous := (2664541)
      next := (2664541)
      square := (34494303555133427766909992492880000000000000)
      linear := (-145451919437464137609692174271975000000000000)
      constant := (3606306475886508514177531382344190865043757170) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree004.checked
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
end ForestUnimodality.Stage99KernelData.Cell107.Kernel004

namespace ForestUnimodality.Stage99KernelData.Cell107.Kernel005
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (86522207272847485359/100000000000000000000)
  centralHi := (1081527590910593567/1250000000000000000)
  directionLo := (49953619659859091769/50000000000000000000)
  directionHi := (99907239319718183539/100000000000000000000)

def endpointA : IntegerEndpointWitness 5 where
  qNumerator := 22647
  qDenominator := 43472
  table := BinomialMassData.Q22647_43472.Degree005.table
  base := (56576792993380087082121870613381007831643/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (900614858)
      previous := (450307429)
      next := (450307429)
      square := (5829537300817549292607788731296720000000000000)
      linear := (-30628419725451005132943931285444965000000000000)
      constant := (457882512038779219147897256889444937597885642227) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22647_43472.Degree005.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 5 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree005.table
  base := (3528468640231258726415991697344503734453/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (5329082)
      previous := (2664541)
      next := (2664541)
      square := (34494303555133427766909992492880000000000000)
      linear := (-181431623624158334993359056393735000000000000)
      constant := (2704587106442374165537300592846459281994263888) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree005.checked
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
end ForestUnimodality.Stage99KernelData.Cell107.Kernel005

namespace ForestUnimodality.Stage99KernelData.Cell107.Kernel006
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (49953619659859091769/50000000000000000000)
  centralHi := (99907239319718183539/100000000000000000000)
  directionLo := (111699689281614851841/100000000000000000000)
  directionHi := (55849844640807425921/50000000000000000000)

def endpointA : IntegerEndpointWitness 6 where
  qNumerator := 22647
  qDenominator := 43472
  table := BinomialMassData.Q22647_43472.Degree006.table
  base := (42685404416035084840694663062688981441961/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (900614858)
      previous := (450307429)
      next := (450307429)
      square := (5829537300817549292607788731296720000000000000)
      linear := (-36702284799595973794596884515003155000000000000)
      constant := (372873213075260642300190451565449478448904436529) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22647_43472.Degree006.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 6 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree006.table
  base := (42597602949886262813477193101923283909829/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (5329082)
      previous := (2664541)
      next := (2664541)
      square := (34494303555133427766909992492880000000000000)
      linear := (-217411327810852532377025938515495000000000000)
      constant := (2203264883803281084748896989905400964465240549) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree006.checked
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
end ForestUnimodality.Stage99KernelData.Cell107.Kernel006

namespace ForestUnimodality.Stage99KernelData.Cell107.Kernel007
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (111699689281614851841/100000000000000000000)
  centralHi := (55849844640807425921/50000000000000000000)
  directionLo := (122360878971716955297/100000000000000000000)
  directionHi := (61180439485858477649/50000000000000000000)

def endpointA : IntegerEndpointWitness 7 where
  qNumerator := 22647
  qDenominator := 43472
  table := BinomialMassData.Q22647_43472.Degree007.table
  base := (4182797972590701928230923434400162025403/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (900614858)
      previous := (450307429)
      next := (450307429)
      square := (5829537300817549292607788731296720000000000000)
      linear := (-42776149873740942456249837744561345000000000000)
      constant := (325490438305465680709959492275002771487561654936) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22647_43472.Degree007.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 7 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree007.table
  base := (1335831682062495452202433607080162908803/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (5329082)
      previous := (2664541)
      next := (2664541)
      square := (34494303555133427766909992492880000000000000)
      linear := (-253391031997546729760692820637255000000000000)
      constant := (1924089618362963106690531045130879900485596075) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree007.checked
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
end ForestUnimodality.Stage99KernelData.Cell107.Kernel007

namespace ForestUnimodality.Stage99KernelData.Cell107.Kernel008
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (122360878971716955297/100000000000000000000)
  centralHi := (61180439485858477649/50000000000000000000)
  directionLo := (26432970941498819983/20000000000000000000)
  directionHi := (33041213676873524979/25000000000000000000)

def endpointA : IntegerEndpointWitness 8 where
  qNumerator := 22647
  qDenominator := 43472
  table := BinomialMassData.Q22647_43472.Degree008.table
  base := (107404945741009045429209109705929356021/40000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (900614858)
      previous := (450307429)
      next := (450307429)
      square := (5829537300817549292607788731296720000000000000)
      linear := (-48850014947885911117902790974119535000000000000)
      constant := (300552961178834188789638162551709345964926967250) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22647_43472.Degree008.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 8 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree008.table
  base := (26797962721807894418531820084261069605019/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (5329082)
      previous := (2664541)
      next := (2664541)
      square := (34494303555133427766909992492880000000000000)
      linear := (-289370736184240927144359702759015000000000000)
      constant := (1777423406538700817893264394656407781416834939) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree008.checked
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
end ForestUnimodality.Stage99KernelData.Cell107.Kernel008

namespace ForestUnimodality.Stage99KernelData.Cell107.Kernel009
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (26432970941498819983/20000000000000000000)
  centralHi := (33041213676873524979/25000000000000000000)
  directionLo := (141290172825200005507/100000000000000000000)
  directionHi := (35322543206300001377/25000000000000000000)

def endpointA : IntegerEndpointWitness 9 where
  qNumerator := 22647
  qDenominator := 43472
  table := BinomialMassData.Q22647_43472.Degree009.table
  base := (10898669414320818828757584632442624714737/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (900614858)
      previous := (450307429)
      next := (450307429)
      square := (5829537300817549292607788731296720000000000000)
      linear := (-54923880022030879779555744203677725000000000000)
      constant := (290275456780584602003732444888547081700576291186) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22647_43472.Degree009.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 9 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree009.table
  base := (21752634187133240080813093526977376092873/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (5329082)
      previous := (2664541)
      next := (2664541)
      square := (34494303555133427766909992492880000000000000)
      linear := (-325350440370935124528026584880775000000000000)
      constant := (1717336516663697312658018884962093765112785513) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree009.checked
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
end ForestUnimodality.Stage99KernelData.Cell107.Kernel009

namespace ForestUnimodality.Stage99KernelData.Cell107.Kernel010
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (141290172825200005507/100000000000000000000)
  centralHi := (35322543206300001377/25000000000000000000)
  directionLo := (149860858979577275307/100000000000000000000)
  directionHi := (37465214744894318827/25000000000000000000)

def endpointA : IntegerEndpointWitness 10 where
  qNumerator := 22647
  qDenominator := 43472
  table := BinomialMassData.Q22647_43472.Degree010.table
  base := (8871981224976849963615523294542060277251/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (900614858)
      previous := (450307429)
      next := (450307429)
      square := (5829537300817549292607788731296720000000000000)
      linear := (-60997745096175848441208697433235915000000000000)
      constant := (290548105694120038932990274514468415795063114678) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22647_43472.Degree010.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 10 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree010.table
  base := (1770507948859617061307774487736050832769/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (5329082)
      previous := (2664541)
      next := (2664541)
      square := (34494303555133427766909992492880000000000000)
      linear := (-361330144557629321911693467002535000000000000)
      constant := (1719597920444396051720956014510334364261826890) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree010.checked
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
end ForestUnimodality.Stage99KernelData.Cell107.Kernel010

namespace ForestUnimodality.Stage99KernelData.Cell107.Kernel011
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (149860858979577275307/100000000000000000000)
  centralHi := (37465214744894318827/25000000000000000000)
  directionLo := (78983607747460180879/50000000000000000000)
  directionHi := (157967215494920361759/100000000000000000000)

def endpointA : IntegerEndpointWitness 11 where
  qNumerator := 22647
  qDenominator := 43472
  table := BinomialMassData.Q22647_43472.Degree011.table
  base := (7192194591931137316399138219524279827803/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 610090000000000000000000000000000000000000000
      center := (7443098)
      previous := (3721549)
      next := (3721549)
      square := (48177994221632638781882551498320000000000000)
      linear := (-554310827853891050436873145973505000000000000)
      constant := (2471956094993309277045874396059467326028866454) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22647_43472.Degree011.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 11 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree011.table
  base := (2869954082022219444652231397834312134449/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (44042)
      previous := (22021)
      next := (22021)
      square := (285076888885400229478594979280000000000000)
      linear := (-3283552468961351399135209496895000000000000)
      constant := (14635221817140185380627282989555933402680445) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree011.checked
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
end ForestUnimodality.Stage99KernelData.Cell107.Kernel011

namespace ForestUnimodality.Stage99KernelData.Cell107.Kernel012
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (78983607747460180879/50000000000000000000)
  centralHi := (157967215494920361759/100000000000000000000)
  directionLo := (82838706665936770279/50000000000000000000)
  directionHi := (165677413331873540559/100000000000000000000)

def endpointA : IntegerEndpointWitness 12 where
  qNumerator := 22647
  qDenominator := 43472
  table := BinomialMassData.Q22647_43472.Degree012.table
  base := (11539560867789568574282684663830127717871/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (900614858)
      previous := (450307429)
      next := (450307429)
      square := (5829537300817549292607788731296720000000000000)
      linear := (-73145475244465785764514603892352295000000000000)
      constant := (314629378888470013946905159390927662444690612519) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22647_43472.Degree012.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 12 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree012.table
  base := (11508322312889786605733218942178717524671/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (5329082)
      previous := (2664541)
      next := (2664541)
      square := (34494303555133427766909992492880000000000000)
      linear := (-433289552931017716679027231246055000000000000)
      constant := (1863336255545487631639625691533248560195153951) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree012.checked
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
end ForestUnimodality.Stage99KernelData.Cell107.Kernel012

namespace ForestUnimodality.Stage99KernelData.Cell107.Kernel013
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (82838706665936770279/50000000000000000000)
  centralHi := (165677413331873540559/100000000000000000000)
  directionLo := (86522207272847485359/50000000000000000000)
  directionHi := (173044414545694970719/100000000000000000000)

def endpointA : IntegerEndpointWitness 13 where
  qNumerator := 22647
  qDenominator := 43472
  table := BinomialMassData.Q22647_43472.Degree013.table
  base := (9097343762264425391115717450311703574403/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (5329082)
      previous := (2664541)
      next := (2664541)
      square := (34494303555133427766909992492880000000000000)
      linear := (-468753493009531091279097971135565000000000000)
      constant := (1989872181256094224966983385017424898833497443) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22647_43472.Degree013.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 13 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree013.table
  base := (3627587040152221959748951055220816823/4000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (5329082)
      previous := (2664541)
      next := (2664541)
      square := (34494303555133427766909992492880000000000000)
      linear := (-469269257117711914062694113367815000000000000)
      constant := (1992139047073997550734478803013126249113657500) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree013.checked
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
end ForestUnimodality.Stage99KernelData.Cell107.Kernel013

namespace ForestUnimodality.Stage99KernelData.Cell107.Kernel014
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (86522207272847485359/50000000000000000000)
  centralHi := (173044414545694970719/100000000000000000000)
  directionLo := (180110337078647959323/100000000000000000000)
  directionHi := (45027584269661989831/25000000000000000000)

def endpointA : IntegerEndpointWitness 14 where
  qNumerator := 22647
  qDenominator := 43472
  table := BinomialMassData.Q22647_43472.Degree014.table
  base := (872761948998107965871021416125591121321/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (900614858)
      previous := (450307429)
      next := (450307429)
      square := (5829537300817549292607788731296720000000000000)
      linear := (-85293205392755723087820510351468675000000000000)
      constant := (363525348717178424491333006643373661306611356552) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22647_43472.Degree014.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 14 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree014.table
  base := (3478127881939955388075618954788839671801/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (5329082)
      previous := (2664541)
      next := (2664541)
      square := (34494303555133427766909992492880000000000000)
      linear := (-505248961304406111446360995489575000000000000)
      constant := (2153974460788814983640895927876832611407878962) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree014.checked
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
end ForestUnimodality.Stage99KernelData.Cell107.Kernel014

namespace ForestUnimodality.Stage99KernelData.Cell107.Kernel015
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (180110337078647959323/100000000000000000000)
  centralHi := (45027584269661989831/25000000000000000000)
  directionLo := (186909329996407752051/100000000000000000000)
  directionHi := (46727332499101938013/25000000000000000000)

def endpointA : IntegerEndpointWitness 15 where
  qNumerator := 22647
  qDenominator := 43472
  table := BinomialMassData.Q22647_43472.Degree015.table
  base := (1027836652747996535550680987998489068141/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (900614858)
      previous := (450307429)
      next := (450307429)
      square := (5829537300817549292607788731296720000000000000)
      linear := (-91367070466900691749473463581026865000000000000)
      constant := (395936922786737349118495552887227678332719632745) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22647_43472.Degree015.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 15 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree015.table
  base := (127891264206772076913578655071948780049/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (5329082)
      previous := (2664541)
      next := (2664541)
      square := (34494303555133427766909992492880000000000000)
      linear := (-541228665491100308830027877611335000000000000)
      constant := (2346460299403795513139593312237436786452814760) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree015.checked
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
end ForestUnimodality.Stage99KernelData.Cell107.Kernel015

namespace ForestUnimodality.Stage99KernelData.Cell107.Kernel016
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (186909329996407752051/100000000000000000000)
  centralHi := (46727332499101938013/25000000000000000000)
  directionLo := (193469537025413671321/100000000000000000000)
  directionHi := (96734768512706835661/50000000000000000000)

def endpointA : IntegerEndpointWitness 16 where
  qNumerator := 22647
  qDenominator := 43472
  table := BinomialMassData.Q22647_43472.Degree016.table
  base := (3526915327266866952760843917072743210503/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (900614858)
      previous := (450307429)
      next := (450307429)
      square := (5829537300817549292607788731296720000000000000)
      linear := (-97440935541045660411126416810585055000000000000)
      constant := (433215350844576783825421497587084294854078880767) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22647_43472.Degree016.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 16 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree016.table
  base := (87637697872060925959354074443135619831/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (5329082)
      previous := (2664541)
      next := (2664541)
      square := (34494303555133427766909992492880000000000000)
      linear := (-577208369677794506213694759733095000000000000)
      constant := (2567777507044889669784051103038264280393516440) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree016.checked
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
end ForestUnimodality.Stage99KernelData.Cell107.Kernel016

namespace ForestUnimodality.Stage99KernelData.Cell107.Kernel017
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (193469537025413671321/100000000000000000000)
  centralHi := (96734768512706835661/50000000000000000000)
  directionLo := (49953619659859091769/25000000000000000000)
  directionHi := (199814478639436367077/100000000000000000000)

def endpointA : IntegerEndpointWitness 17 where
  qNumerator := 22647
  qDenominator := 43472
  table := BinomialMassData.Q22647_43472.Degree017.table
  base := (264022885029794314735347087542540108409/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (900614858)
      previous := (450307429)
      next := (450307429)
      square := (5829537300817549292607788731296720000000000000)
      linear := (-103514800615190629072779370040143245000000000000)
      constant := (475116221503443111358906678421393742055759091208) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22647_43472.Degree017.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 17 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree017.table
  base := (2092741935677663459475594666383163493139/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (5329082)
      previous := (2664541)
      next := (2664541)
      square := (34494303555133427766909992492880000000000000)
      linear := (-613188073864488703597361641854855000000000000)
      constant := (2816480859910377222714338596546997964543804659) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree017.checked
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
end ForestUnimodality.Stage99KernelData.Cell107.Kernel017

namespace ForestUnimodality.Stage99KernelData.Cell107.Kernel018
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (49953619659859091769/25000000000000000000)
  centralHi := (199814478639436367077/100000000000000000000)
  directionLo := (41192810047905997633/20000000000000000000)
  directionHi := (102982025119764994083/50000000000000000000)

def endpointA : IntegerEndpointWitness 18 where
  qNumerator := 22647
  qDenominator := 43472
  table := BinomialMassData.Q22647_43472.Degree018.table
  base := (108497794420559666911193215693379545203/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (900614858)
      previous := (450307429)
      next := (450307429)
      square := (5829537300817549292607788731296720000000000000)
      linear := (-109588665689335597734432323269701435000000000000)
      constant := (521440187597030898856537196411353017982744552536) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22647_43472.Degree018.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 18 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree018.table
  base := (85036003632310792710778851484603509133/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (5329082)
      previous := (2664541)
      next := (2664541)
      square := (34494303555133427766909992492880000000000000)
      linear := (-649167778051182900981028523976615000000000000)
      constant := (3091391294487178549727575020815939658824385730) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree018.checked
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
end ForestUnimodality.Stage99KernelData.Cell107.Kernel018

namespace ForestUnimodality.Stage99KernelData.Cell107.Kernel019
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (41192810047905997633/20000000000000000000)
  centralHi := (102982025119764994083/50000000000000000000)
  directionLo := (211935259237800008261/100000000000000000000)
  directionHi := (105967629618900004131/50000000000000000000)

def endpointA : IntegerEndpointWitness 19 where
  qNumerator := 22647
  qDenominator := 43472
  table := BinomialMassData.Q22647_43472.Degree019.table
  base := (-57022471818090628964665296450281490001/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 204490000000000000000000000000000000000000000
      center := (2494778)
      previous := (1247389)
      next := (1247389)
      square := (16148302772347781973982794269520000000000000)
      linear := (-320394822059502954005776389194625000000000000)
      constant := (1584548110500825168422323000864364025243878204) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22647_43472.Degree019.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 19 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree019.table
  base := (-3050422246103881743807759822219508821/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (14762)
      previous := (7381)
      next := (7381)
      square := (95552087410341905171495824080000000000000)
      linear := (-1897915463262817446993616083375000000000000)
      constant := (9394821416210160239619145827665915154612720) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree019.checked
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
end ForestUnimodality.Stage99KernelData.Cell107.Kernel019

namespace ForestUnimodality.Stage99KernelData.Cell107.Kernel020
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (211935259237800008261/100000000000000000000)
  centralHi := (105967629618900004131/50000000000000000000)
  directionLo := (21774277996139241563/10000000000000000000)
  directionHi := (217742779961392415631/100000000000000000000)

def endpointA : IntegerEndpointWitness 20 where
  qNumerator := 22647
  qDenominator := 43472
  table := BinomialMassData.Q22647_43472.Degree020.table
  base := (-1194816557591240102377701797224767861343/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (900614858)
      previous := (450307429)
      next := (450307429)
      square := (5829537300817549292607788731296720000000000000)
      linear := (-121736395837625535057738229728817815000000000000)
      constant := (626722605272042477249755290501790891893226314473) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22647_43472.Degree020.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 20 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree020.table
  base := (-1209216694616194457315028140242920812207/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (5329082)
      previous := (2664541)
      next := (2664541)
      square := (34494303555133427766909992492880000000000000)
      linear := (-721127186424571295748362288220135000000000000)
      constant := (3716078364106163415496107222626748976001986033) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree020.checked
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
end ForestUnimodality.Stage99KernelData.Cell107.Kernel020

namespace ForestUnimodality.Stage99KernelData.Cell107.Kernel021
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (21774277996139241563/10000000000000000000)
  centralHi := (217742779961392415631/100000000000000000000)
  directionLo := (223399378563229703683/100000000000000000000)
  directionHi := (55849844640807425921/25000000000000000000)

def endpointA : IntegerEndpointWitness 21 where
  qNumerator := 22647
  qDenominator := 43472
  table := BinomialMassData.Q22647_43472.Degree021.table
  base := (-409609559131999603498927511522932513653/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (900614858)
      previous := (450307429)
      next := (450307429)
      square := (5829537300817549292607788731296720000000000000)
      linear := (-127810260911770503719391182958376005000000000000)
      constant := (685425392596121393143234293156438815091099194415) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22647_43472.Degree021.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 21 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree021.table
  base := (-257629132156141225985577156603940424631/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (5329082)
      previous := (2664541)
      next := (2664541)
      square := (34494303555133427766909992492880000000000000)
      linear := (-757106890611265493132029170341895000000000000)
      constant := (4064342696050631032447787691947281226493546312) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree021.checked
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
end ForestUnimodality.Stage99KernelData.Cell107.Kernel021

namespace ForestUnimodality.Stage99KernelData.Cell107.Kernel022
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (223399378563229703683/100000000000000000000)
  centralHi := (55849844640807425921/25000000000000000000)
  directionLo := (228916243328338489551/100000000000000000000)
  directionHi := (14307265208021155597/6250000000000000000)

def endpointA : IntegerEndpointWitness 22 where
  qNumerator := 22647
  qDenominator := 43472
  table := BinomialMassData.Q22647_43472.Degree022.table
  base := (-700303179625853654179206929492988165733/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 610090000000000000000000000000000000000000000
      center := (7443098)
      previous := (3721549)
      next := (3721549)
      square := (48177994221632638781882551498320000000000000)
      linear := (-1106480380048888201496232530478795000000000000)
      constant := (6182075164677407474836914422562937264987181612) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22647_43472.Degree022.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 22 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree022.table
  base := (-703226416552342700947362600506943957729/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (44042)
      previous := (22021)
      next := (22021)
      square := (285076888885400229478594979280000000000000)
      linear := (-6554434667751732979468562417055000000000000)
      constant := (36658985172054975298330727895557972925039324) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree022.checked
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
end ForestUnimodality.Stage99KernelData.Cell107.Kernel022

namespace ForestUnimodality.Stage99KernelData.Cell107.Kernel023
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (228916243328338489551/100000000000000000000)
  centralHi := (14307265208021155597/6250000000000000000)
  directionLo := (234303244912828590539/100000000000000000000)
  directionHi := (11715162245641429527/5000000000000000000)

def endpointA : IntegerEndpointWitness 23 where
  qNumerator := 22647
  qDenominator := 43472
  table := BinomialMassData.Q22647_43472.Degree023.table
  base := (-693143668545034962205845520964507494463/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (900614858)
      previous := (450307429)
      next := (450307429)
      square := (5829537300817549292607788731296720000000000000)
      linear := (-139957991060060441042697089417492385000000000000)
      constant := (814455504649784331445004328541382424173535633965) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22647_43472.Degree023.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 23 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree023.table
  base := (-695246931345279163904950091048243204063/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (5329082)
      previous := (2664541)
      next := (2664541)
      square := (34494303555133427766909992492880000000000000)
      linear := (-829066298984653887899362934585415000000000000)
      constant := (4829763924103267506570472542801133443016620485) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree023.checked
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
end ForestUnimodality.Stage99KernelData.Cell107.Kernel023

namespace ForestUnimodality.Stage99KernelData.Cell107.Kernel024
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (234303244912828590539/100000000000000000000)
  centralHi := (11715162245641429527/5000000000000000000)
  directionLo := (47913828773665248617/20000000000000000000)
  directionHi := (119784571934163121543/50000000000000000000)

def endpointA : IntegerEndpointWitness 24 where
  qNumerator := 22647
  qDenominator := 43472
  table := BinomialMassData.Q22647_43472.Degree024.table
  base := (-1012817652151501295070982140355949684841/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (900614858)
      previous := (450307429)
      next := (450307429)
      square := (5829537300817549292607788731296720000000000000)
      linear := (-146031856134205409704350042647050575000000000000)
      constant := (884626971652594465515313598258184318487927148604) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22647_43472.Degree024.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 24 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree024.table
  base := (-2030359332454675961321837720809115222571/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (5329082)
      previous := (2664541)
      next := (2664541)
      square := (34494303555133427766909992492880000000000000)
      linear := (-865046003171348085283029816707175000000000000)
      constant := (5245999204780593865807361598391994075925752298) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree024.checked
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
end ForestUnimodality.Stage99KernelData.Cell107.Kernel024

namespace ForestUnimodality.Stage99KernelData.Cell107.Kernel025
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (47913828773665248617/20000000000000000000)
  centralHi := (119784571934163121543/50000000000000000000)
  directionLo := (122360878971716955297/50000000000000000000)
  directionHi := (48944351588686782119/20000000000000000000)

def endpointA : IntegerEndpointWitness 25 where
  qNumerator := 22647
  qDenominator := 43472
  table := BinomialMassData.Q22647_43472.Degree025.table
  base := (-4566138116437099147477472583982943553447/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (900614858)
      previous := (450307429)
      next := (450307429)
      square := (5829537300817549292607788731296720000000000000)
      linear := (-152105721208350378366002995876608765000000000000)
      constant := (958484456391141690901419334572281826831477989217) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22647_43472.Degree025.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 25 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree025.table
  base := (-228730937797637016954473348125157506603/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (5329082)
      previous := (2664541)
      next := (2664541)
      square := (34494303555133427766909992492880000000000000)
      linear := (-901025707358042282666696698828935000000000000)
      constant := (5684082196261870080758258505746774899081487140) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree025.checked
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
end ForestUnimodality.Stage99KernelData.Cell107.Kernel025

namespace ForestUnimodality.Stage99KernelData.Cell107.Kernel026
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (122360878971716955297/50000000000000000000)
  centralHi := (48944351588686782119/20000000000000000000)
  directionLo := (49953619659859091769/20000000000000000000)
  directionHi := (124884049149647729423/50000000000000000000)

def endpointA : IntegerEndpointWitness 26 where
  qNumerator := 22647
  qDenominator := 43472
  table := BinomialMassData.Q22647_43472.Degree026.table
  base := (-1254342905100873053905969811973149674741/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (5329082)
      previous := (2664541)
      next := (2664541)
      square := (34494303555133427766909992492880000000000000)
      linear := (-935973883328374834483171296486195000000000000)
      constant := (6130034967872869544685871459943102771230553516) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22647_43472.Degree026.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 26 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree026.table
  base := (-5024978104226739450226404219807623789023/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (5329082)
      previous := (2664541)
      next := (2664541)
      square := (34494303555133427766909992492880000000000000)
      linear := (-937005411544736480050363580950695000000000000)
      constant := (6143705245647432389546790185046773185271686337) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree026.checked
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
end ForestUnimodality.Stage99KernelData.Cell107.Kernel026

namespace ForestUnimodality.Stage99KernelData.Cell107.Kernel027
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (49953619659859091769/20000000000000000000)
  centralHi := (124884049149647729423/50000000000000000000)
  directionLo := (2547144814202136797/1000000000000000000)
  directionHi := (254714481420213679701/100000000000000000000)

def endpointA : IntegerEndpointWitness 27 where
  qNumerator := 22647
  qDenominator := 43472
  table := BinomialMassData.Q22647_43472.Degree027.table
  base := (-676373519669952902079242793881615162807/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (900614858)
      previous := (450307429)
      next := (450307429)
      square := (5829537300817549292607788731296720000000000000)
      linear := (-164253451356640315689308902335725145000000000000)
      constant := (1117056912889138504464570904855744969985273889416) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22647_43472.Degree027.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 27 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree027.table
  base := (-5417806279471761119701924876040349838047/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (5329082)
      previous := (2664541)
      next := (2664541)
      square := (34494303555133427766909992492880000000000000)
      linear := (-972985115731430677434030463072455000000000000)
      constant := (6624605848921449861556972911755946478724268993) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree027.checked
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
end ForestUnimodality.Stage99KernelData.Cell107.Kernel027

namespace ForestUnimodality.Stage99KernelData.Cell107.Kernel028
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (2547144814202136797/1000000000000000000)
  centralHi := (254714481420213679701/100000000000000000000)
  directionLo := (259566621818542456077/100000000000000000000)
  directionHi := (129783310909271228039/50000000000000000000)

def endpointA : IntegerEndpointWitness 28 where
  qNumerator := 22647
  qDenominator := 43472
  table := BinomialMassData.Q22647_43472.Degree028.table
  base := (-5752126258830796948259867350276080703813/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (900614858)
      previous := (450307429)
      next := (450307429)
      square := (5829537300817549292607788731296720000000000000)
      linear := (-170327316430785284350961855565283335000000000000)
      constant := (1201689533249963239370261438319890541423269794643) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22647_43472.Degree028.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 28 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree028.table
  base := (-5758234581123188261556916466247212131127/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (5329082)
      previous := (2664541)
      next := (2664541)
      square := (34494303555133427766909992492880000000000000)
      linear := (-1008964819918124874817697345194215000000000000)
      constant := (7126559865793285535720586677455955526900241513) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree028.checked
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
end ForestUnimodality.Stage99KernelData.Cell107.Kernel028

namespace ForestUnimodality.Stage99KernelData.Cell107.Kernel029
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (259566621818542456077/100000000000000000000)
  centralHi := (129783310909271228039/50000000000000000000)
  directionLo := (26432970941498819983/10000000000000000000)
  directionHi := (264329709414988199831/100000000000000000000)

def endpointA : IntegerEndpointWitness 29 where
  qNumerator := 22647
  qDenominator := 43472
  table := BinomialMassData.Q22647_43472.Degree029.table
  base := (-3022588589564291093330620856760807724693/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (900614858)
      previous := (450307429)
      next := (450307429)
      square := (5829537300817549292607788731296720000000000000)
      linear := (-176401181504930253012614808794841525000000000000)
      constant := (1289841354022839523333752724231059120703857552646) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22647_43472.Degree029.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 29 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree029.table
  base := (-1512661838766548963313654710465398345227/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (5329082)
      previous := (2664541)
      next := (2664541)
      square := (34494303555133427766909992492880000000000000)
      linear := (-1044944524104819072201364227315975000000000000)
      constant := (7649375783650329083847059702196338739528557652) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree029.checked
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
end ForestUnimodality.Stage99KernelData.Cell107.Kernel029

namespace ForestUnimodality.Stage99KernelData.Cell107.Kernel030
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (26432970941498819983/10000000000000000000)
  centralHi := (264329709414988199831/100000000000000000000)
  directionLo := (134504237290627727397/50000000000000000000)
  directionHi := (53801694916251090959/20000000000000000000)

def endpointA : IntegerEndpointWitness 30 where
  qNumerator := 22647
  qDenominator := 43472
  table := BinomialMassData.Q22647_43472.Degree030.table
  base := (-3146948027946292443729835043782293296207/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (900614858)
      previous := (450307429)
      next := (450307429)
      square := (5829537300817549292607788731296720000000000000)
      linear := (-182475046579075221674267762024399715000000000000)
      constant := (1381484654447504535265716026763943644151593127154) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22647_43472.Degree030.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 30 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree030.table
  base := (-6298793213638828985148787740508793811387/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (5329082)
      previous := (2664541)
      next := (2664541)
      square := (34494303555133427766909992492880000000000000)
      linear := (-1080924228291513269585031109437735000000000000)
      constant := (8192889859357042358344649581601885377524804453) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree030.checked
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
end ForestUnimodality.Stage99KernelData.Cell107.Kernel030

namespace ForestUnimodality.Stage99KernelData.Cell107.Kernel031
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (134504237290627727397/50000000000000000000)
  centralHi := (53801694916251090959/20000000000000000000)
  directionLo := (273607243167383679001/100000000000000000000)
  directionHi := (136803621583691839501/50000000000000000000)

def endpointA : IntegerEndpointWitness 31 where
  qNumerator := 22647
  qDenominator := 43472
  table := BinomialMassData.Q22647_43472.Degree031.table
  base := (-1300299238023174696270035031581364103393/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (900614858)
      previous := (450307429)
      next := (450307429)
      square := (5829537300817549292607788731296720000000000000)
      linear := (-188548911653220190335920715253957905000000000000)
      constant := (1476595713650043655627670356597150619736738360115) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22647_43472.Degree031.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 31 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree031.table
  base := (-3252939675637861452786606280555190648033/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (5329082)
      previous := (2664541)
      next := (2664541)
      square := (34494303555133427766909992492880000000000000)
      linear := (-1116903932478207466968697991559495000000000000)
      constant := (8756961999453326056930888060938302434606541054) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree031.checked
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
end ForestUnimodality.Stage99KernelData.Cell107.Kernel031

namespace ForestUnimodality.Stage99KernelData.Cell107.Kernel032
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (273607243167383679001/100000000000000000000)
  centralHi := (136803621583691839501/50000000000000000000)
  directionLo := (278129983336528612501/100000000000000000000)
  directionHi := (139064991668264306251/50000000000000000000)

def endpointA : IntegerEndpointWitness 32 where
  qNumerator := 22647
  qDenominator := 43472
  table := BinomialMassData.Q22647_43472.Degree032.table
  base := (-1667682270060308459801459409279657034783/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (900614858)
      previous := (450307429)
      next := (450307429)
      square := (5829537300817549292607788731296720000000000000)
      linear := (-194622776727365158997573668483516095000000000000)
      constant := (1575154219824068877712888124206302593519023193252) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22647_43472.Degree032.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 32 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree032.table
  base := (-6674651595504964228097091903587320249033/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (5329082)
      previous := (2664541)
      next := (2664541)
      square := (34494303555133427766909992492880000000000000)
      linear := (-1152883636664901664352364873681255000000000000)
      constant := (9341472263446925828238458976162442264201989527) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree032.checked
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
end ForestUnimodality.Stage99KernelData.Cell107.Kernel032

namespace ForestUnimodality.Stage99KernelData.Cell107.Kernel033
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (278129983336528612501/100000000000000000000)
  centralHi := (139064991668264306251/50000000000000000000)
  directionLo := (56516069130080002203/20000000000000000000)
  directionHi := (35322543206300001377/12500000000000000000)

def endpointA : IntegerEndpointWitness 33 where
  qNumerator := 22647
  qDenominator := 43472
  table := BinomialMassData.Q22647_43472.Degree033.table
  base := (-6803952409360971416195851716083133687657/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 610090000000000000000000000000000000000000000
      center := (7443098)
      previous := (3721549)
      next := (3721549)
      square := (48177994221632638781882551498320000000000000)
      linear := (-1658649932243885352555591914984085000000000000)
      constant := (13860684035893876094513428330710887221849734087) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22647_43472.Degree033.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 33 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree033.table
  base := (-6807462396828106948287652662353181727847/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (44042)
      previous := (22021)
      next := (22021)
      square := (285076888885400229478594979280000000000000)
      linear := (-9825316866542114559801915337215000000000000)
      constant := (82200974330144490018074299911565501396247233) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree033.checked
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
end ForestUnimodality.Stage99KernelData.Cell107.Kernel033

namespace ForestUnimodality.Stage99KernelData.Cell107.Kernel034
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (56516069130080002203/20000000000000000000)
  centralHi := (35322543206300001377/12500000000000000000)
  directionLo := (7174042438934856081/2500000000000000000)
  directionHi := (286961697557394243241/100000000000000000000)

def endpointA : IntegerEndpointWitness 34 where
  qNumerator := 22647
  qDenominator := 43472
  table := BinomialMassData.Q22647_43472.Degree034.table
  base := (-1725796957953516073889569312405734541723/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (900614858)
      previous := (450307429)
      next := (450307429)
      square := (5829537300817549292607788731296720000000000000)
      linear := (-206770506875655096320879574942632475000000000000)
      constant := (1782546435175056472417867701990667380885506402612) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22647_43472.Degree034.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 34 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree034.table
  base := (-1381265721506356984338059141937357865591/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (5329082)
      previous := (2664541)
      next := (2664541)
      square := (34494303555133427766909992492880000000000000)
      linear := (-1224843045038290059119698637924775000000000000)
      constant := (10571410792830265995332403344847241355365597645) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree034.checked
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
end ForestUnimodality.Stage99KernelData.Cell107.Kernel034

namespace ForestUnimodality.Stage99KernelData.Cell107.Kernel035
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (7174042438934856081/2500000000000000000)
  centralHi := (286961697557394243241/100000000000000000000)
  directionLo := (36409644151254603143/12500000000000000000)
  directionHi := (58255430642007365029/20000000000000000000)

def endpointA : IntegerEndpointWitness 35 where
  qNumerator := 22647
  qDenominator := 43472
  table := BinomialMassData.Q22647_43472.Degree035.table
  base := (-697017011484924317826728900108140915733/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (900614858)
      previous := (450307429)
      next := (450307429)
      square := (5829537300817549292607788731296720000000000000)
      linear := (-212844371949800064982532528172190665000000000000)
      constant := (1891352414113536857486493001325697997605174937630) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22647_43472.Degree035.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 35 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree035.table
  base := (-3486490304068255937754456631009961873257/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (5329082)
      previous := (2664541)
      next := (2664541)
      square := (34494303555133427766909992492880000000000000)
      linear := (-1260822749224984256503365520046535000000000000)
      constant := (11216675375343757377556704926899932710828521966) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree035.checked
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
end ForestUnimodality.Stage99KernelData.Cell107.Kernel035

namespace ForestUnimodality.Stage99KernelData.Cell107.Kernel036
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (36409644151254603143/12500000000000000000)
  centralHi := (58255430642007365029/20000000000000000000)
  directionLo := (147764799681169945673/50000000000000000000)
  directionHi := (295529599362339891347/100000000000000000000)

def endpointA : IntegerEndpointWitness 36 where
  qNumerator := 22647
  qDenominator := 43472
  table := BinomialMassData.Q22647_43472.Degree036.table
  base := (-7006388949011567298699262301908297472921/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (900614858)
      previous := (450307429)
      next := (450307429)
      square := (5829537300817549292607788731296720000000000000)
      linear := (-218918237023945033644185481401748855000000000000)
      constant := (2003549708130414076863562463826942644466422088031) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22647_43472.Degree036.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 36 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree036.table
  base := (-3504452048770730321668749069431053685967/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (5329082)
      previous := (2664541)
      next := (2664541)
      square := (34494303555133427766909992492880000000000000)
      linear := (-1296802453411678453887032402168295000000000000)
      constant := (11882046744674342670315675835108504287886550946) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree036.checked
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
end ForestUnimodality.Stage99KernelData.Cell107.Kernel036

namespace ForestUnimodality.Stage99KernelData.Cell107.Kernel037
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (147764799681169945673/50000000000000000000)
  centralHi := (295529599362339891347/100000000000000000000)
  directionLo := (59944343591830910123/20000000000000000000)
  directionHi := (37465214744894318827/12500000000000000000)

def endpointA : IntegerEndpointWitness 37 where
  qNumerator := 22647
  qDenominator := 43472
  table := BinomialMassData.Q22647_43472.Degree037.table
  base := (-7013124538073367785687750196559894537631/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (900614858)
      previous := (450307429)
      next := (450307429)
      square := (5829537300817549292607788731296720000000000000)
      linear := (-224992102098090002305838434631307045000000000000)
      constant := (2119128866647502646418556334734004021567594108841) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22647_43472.Degree037.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 37 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree037.table
  base := (-7015375659549622816835436698392564064697/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (5329082)
      previous := (2664541)
      next := (2664541)
      square := (34494303555133427766909992492880000000000000)
      linear := (-1332782157598372651270699284290055000000000000)
      constant := (12567469138364923397894042413961329409089970343) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree037.checked
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
end ForestUnimodality.Stage99KernelData.Cell107.Kernel037

namespace ForestUnimodality.Stage99KernelData.Cell107.Kernel038
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (59944343591830910123/20000000000000000000)
  centralHi := (37465214744894318827/12500000000000000000)
  directionLo := (75964001479939845353/25000000000000000000)
  directionHi := (303856005919759381413/100000000000000000000)

def endpointA : IntegerEndpointWitness 38 where
  qNumerator := 22647
  qDenominator := 43472
  table := BinomialMassData.Q22647_43472.Degree038.table
  base := (-279659116346438122965265643007047235091/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 204490000000000000000000000000000000000000000
      center := (2494778)
      previous := (1247389)
      next := (1247389)
      square := (16148302772347781973982794269520000000000000)
      linear := (-640071931225027620408563401276635000000000000)
      constant := (6199672470327578358846538265788925402240603525) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22647_43472.Degree038.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 38 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree038.table
  base := (-1748373261836556237161178490844956186707/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (14762)
      previous := (7381)
      next := (7381)
      square := (95552087410341905171495824080000000000000)
      linear := (-3791584104667775204028715142415000000000000)
      constant := (36767021067752398003451108353681041205633812) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree038.checked
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
end ForestUnimodality.Stage99KernelData.Cell107.Kernel038

namespace ForestUnimodality.Stage99KernelData.Cell107.Kernel039
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (75964001479939845353/25000000000000000000)
  centralHi := (303856005919759381413/100000000000000000000)
  directionLo := (38491849066277717963/12500000000000000000)
  directionHi := (61586958506044348741/20000000000000000000)

def endpointA : IntegerEndpointWitness 39 where
  qNumerator := 22647
  qDenominator := 43472
  table := BinomialMassData.Q22647_43472.Degree039.table
  base := (-3471198367891772124853917649716493035729/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (5329082)
      previous := (2664541)
      next := (2664541)
      square := (34494303555133427766909992492880000000000000)
      linear := (-1403194273647218577687244621836825000000000000)
      constant := (13966872175925516889725153241185287735412643102) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22647_43472.Degree039.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 39 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree039.table
  base := (-3472100491600887434112393321211668074329/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (5329082)
      previous := (2664541)
      next := (2664541)
      square := (34494303555133427766909992492880000000000000)
      linear := (-1404741565971761046038033048533575000000000000)
      constant := (13998281879541921461872480411772751253690469902) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree039.checked
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
end ForestUnimodality.Stage99KernelData.Cell107.Kernel039

namespace ForestUnimodality.Stage99KernelData.Cell107.Kernel040
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (38491849066277717963/12500000000000000000)
  centralHi := (61586958506044348741/20000000000000000000)
  directionLo := (77990063697143725377/25000000000000000000)
  directionHi := (311960254788574901509/100000000000000000000)

def endpointA : IntegerEndpointWitness 40 where
  qNumerator := 22647
  qDenominator := 43472
  table := BinomialMassData.Q22647_43472.Degree040.table
  base := (-137333947177752319442823800772685846783/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (900614858)
      previous := (450307429)
      next := (450307429)
      square := (5829537300817549292607788731296720000000000000)
      linear := (-243213697320524908290797294319981615000000000000)
      constant := (2486081748186524260204074475029448628000376515650) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22647_43472.Degree040.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 40 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree040.table
  base := (-6868313148804212002448730936308327308579/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (5329082)
      previous := (2664541)
      next := (2664541)
      square := (34494303555133427766909992492880000000000000)
      linear := (-1440721270158455243421699930655335000000000000)
      constant := (14743595418185029863668690460716515954833960701) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree040.checked
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
end ForestUnimodality.Stage99KernelData.Cell107.Kernel040

namespace ForestUnimodality.Stage99KernelData.Cell107.Kernel041
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (77990063697143725377/25000000000000000000)
  centralHi := (311960254788574901509/100000000000000000000)
  directionLo := (315934430989840723517/100000000000000000000)
  directionHi := (157967215494920361759/50000000000000000000)

def endpointA : IntegerEndpointWitness 41 where
  qNumerator := 22647
  qDenominator := 43472
  table := BinomialMassData.Q22647_43472.Degree041.table
  base := (-1353016712053629912829275438209998288379/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (900614858)
      previous := (450307429)
      next := (450307429)
      square := (5829537300817549292607788731296720000000000000)
      linear := (-249287562394669876952450247549539805000000000000)
      constant := (2615117617770053328687553616198379785351692781345) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22647_43472.Degree041.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 41 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree041.table
  base := (-6766530938609994289083833042968908888899/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (5329082)
      previous := (2664541)
      next := (2664541)
      square := (34494303555133427766909992492880000000000000)
      linear := (-1476700974345149440805366812777095000000000000)
      constant := (15508804583776688345454867434098190090824002781) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree041.checked
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
end ForestUnimodality.Stage99KernelData.Cell107.Kernel041

namespace ForestUnimodality.Stage99KernelData.Cell107.Kernel042
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (315934430989840723517/100000000000000000000)
  centralHi := (157967215494920361759/50000000000000000000)
  directionLo := (319859232791545805167/100000000000000000000)
  directionHi := (19991202049471612823/6250000000000000000)

def endpointA : IntegerEndpointWitness 42 where
  qNumerator := 22647
  qDenominator := 43472
  table := BinomialMassData.Q22647_43472.Degree042.table
  base := (-6638162590709224885260311958369174969919/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (900614858)
      previous := (450307429)
      next := (450307429)
      square := (5829537300817549292607788731296720000000000000)
      linear := (-255361427468814845614103200779097995000000000000)
      constant := (2747504523702666162507779314462785274890485619209) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22647_43472.Degree042.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 42 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree042.table
  base := (-3319729730735710901825048790747783672837/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (5329082)
      previous := (2664541)
      next := (2664541)
      square := (34494303555133427766909992492880000000000000)
      linear := (-1512680678531843638189033694898855000000000000)
      constant := (16293882944557119587632222010151282122773614006) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree042.checked
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
end ForestUnimodality.Stage99KernelData.Cell107.Kernel042

namespace ForestUnimodality.Stage99KernelData.Cell107.Kernel043
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (319859232791545805167/100000000000000000000)
  centralHi := (19991202049471612823/6250000000000000000)
  directionLo := (12949458238497433113/4000000000000000000)
  directionHi := (161868227981217913913/50000000000000000000)

def endpointA : IntegerEndpointWitness 43 where
  qNumerator := 22647
  qDenominator := 43472
  table := BinomialMassData.Q22647_43472.Degree043.table
  base := (-6486458853627921046903640762561963700339/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (900614858)
      previous := (450307429)
      next := (450307429)
      square := (5829537300817549292607788731296720000000000000)
      linear := (-261435292542959814275756154008656185000000000000)
      constant := (2883238594791665979544203441498150109699328171829) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22647_43472.Degree043.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 43 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree043.table
  base := (-3243810601032772087925040322846295366319/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (5329082)
      previous := (2664541)
      next := (2664541)
      square := (34494303555133427766909992492880000000000000)
      linear := (-1548660382718537835572700577020615000000000000)
      constant := (17098807677873145385325716836142326944207639522) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree043.checked
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
end ForestUnimodality.Stage99KernelData.Cell107.Kernel043

namespace ForestUnimodality.Stage99KernelData.Cell107.Kernel044
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (12949458238497433113/4000000000000000000)
  centralHi := (161868227981217913913/50000000000000000000)
  directionLo := (327567789985889810503/100000000000000000000)
  directionHi := (40945973748236226313/12500000000000000000)

def endpointA : IntegerEndpointWitness 44 where
  qNumerator := 22647
  qDenominator := 43472
  table := BinomialMassData.Q22647_43472.Degree044.table
  base := (-6310425596682785736188420841868910104957/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 610090000000000000000000000000000000000000000
      center := (7443098)
      previous := (3721549)
      next := (3721549)
      square := (48177994221632638781882551498320000000000000)
      linear := (-2210819484438882503614951299489375000000000000)
      constant := (24977822191095027596362154031394118413406678387) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22647_43472.Degree044.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 44 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree044.table
  base := (-6311467691235736852787879930637865892819/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (44042)
      previous := (22021)
      next := (22021)
      square := (285076888885400229478594979280000000000000)
      linear := (-13096199065332496140135268257375000000000000)
      constant := (148128587276082613682895849757459730412692341) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree044.checked
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
end ForestUnimodality.Stage99KernelData.Cell107.Kernel044

namespace ForestUnimodality.Stage99KernelData.Cell107.Kernel045
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (327567789985889810503/100000000000000000000)
  centralHi := (40945973748236226313/12500000000000000000)
  directionLo := (82838706665936770279/25000000000000000000)
  directionHi := (331354826663747081117/100000000000000000000)

def endpointA : IntegerEndpointWitness 45 where
  qNumerator := 22647
  qDenominator := 43472
  table := BinomialMassData.Q22647_43472.Degree045.table
  base := (-3055227453517313782971791829297724584581/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (900614858)
      previous := (450307429)
      next := (450307429)
      square := (5829537300817549292607788731296720000000000000)
      linear := (-273583022691249751599062060467772565000000000000)
      constant := (3164735300272846394862761189534761063613270060582) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22647_43472.Degree045.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 45 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree045.table
  base := (-763923685188414905151603918681821927537/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (5329082)
      previous := (2664541)
      next := (2664541)
      square := (34494303555133427766909992492880000000000000)
      linear := (-1620619791091926230340034341264135000000000000)
      constant := (18768120032430813721540047221661049691066050424) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree045.checked
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
end ForestUnimodality.Stage99KernelData.Cell107.Kernel045

namespace ForestUnimodality.Stage99KernelData.Cell107.Kernel046
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (82838706665936770279/25000000000000000000)
  centralHi := (331354826663747081117/100000000000000000000)
  directionLo := (13403962713793782221/4000000000000000000)
  directionHi := (167549533922422277763/50000000000000000000)

def endpointA : IntegerEndpointWitness 46 where
  qNumerator := 22647
  qDenominator := 43472
  table := BinomialMassData.Q22647_43472.Degree046.table
  base := (-5886886261740391403119681104622079147897/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (900614858)
      previous := (450307429)
      next := (450307429)
      square := (5829537300817549292607788731296720000000000000)
      linear := (-279656887765394720260715013697330755000000000000)
      constant := (3310492534192862321577102964041388100990180183167) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22647_43472.Degree046.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 46 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree046.table
  base := (-5887724679275355106650129071430859075209/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (5329082)
      previous := (2664541)
      next := (2664541)
      square := (34494303555133427766909992492880000000000000)
      linear := (-1656599495278620427723701223385895000000000000)
      constant := (19632475825122155002712759032658918644735795671) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree046.checked
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
end ForestUnimodality.Stage99KernelData.Cell107.Kernel046

namespace ForestUnimodality.Stage99KernelData.Cell107.Kernel047
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (13403962713793782221/4000000000000000000)
  centralHi := (167549533922422277763/50000000000000000000)
  directionLo := (67760386476939635327/20000000000000000000)
  directionHi := (84700483096174544159/25000000000000000000)

def endpointA : IntegerEndpointWitness 47 where
  qNumerator := 22647
  qDenominator := 43472
  table := BinomialMassData.Q22647_43472.Degree047.table
  base := (-2820006923438648360576926654310229771863/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (900614858)
      previous := (450307429)
      next := (450307429)
      square := (5829537300817549292607788731296720000000000000)
      linear := (-285730752839539688922367966926888945000000000000)
      constant := (3459586015174741524277399856983243797927315276386) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22647_43472.Degree047.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 47 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree047.table
  base := (-5640766247238580769788944259597632513843/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (5329082)
      previous := (2664541)
      next := (2664541)
      square := (34494303555133427766909992492880000000000000)
      linear := (-1692579199465314625107368105507655000000000000)
      constant := (20516613641576376597924509568073880814162823917) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree047.checked
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
end ForestUnimodality.Stage99KernelData.Cell107.Kernel047

namespace ForestUnimodality.Stage99KernelData.Cell107.Kernel048
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (67760386476939635327/20000000000000000000)
  centralHi := (84700483096174544159/25000000000000000000)
  directionLo := (342464762427797023523/100000000000000000000)
  directionHi := (85616190606949255881/25000000000000000000)

def endpointA : IntegerEndpointWitness 48 where
  qNumerator := 22647
  qDenominator := 43472
  table := BinomialMassData.Q22647_43472.Degree048.table
  base := (-5370092826884259701644839675157962144079/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (900614858)
      previous := (450307429)
      next := (450307429)
      square := (5829537300817549292607788731296720000000000000)
      linear := (-291804617913684657584020920156447135000000000000)
      constant := (3612013859571886288647549811788004809393777998969) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22647_43472.Degree048.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 48 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree048.table
  base := (-5370768258514765720382131340588276224717/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (5329082)
      previous := (2664541)
      next := (2664541)
      square := (34494303555133427766909992492880000000000000)
      linear := (-1728558903652008822491034987629415000000000000)
      constant := (21420522383625621218093404393696163506228136723) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree048.checked
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
end ForestUnimodality.Stage99KernelData.Cell107.Kernel048

namespace ForestUnimodality.Stage99KernelData.Cell107.Kernel049
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (342464762427797023523/100000000000000000000)
  centralHi := (85616190606949255881/25000000000000000000)
  directionLo := (86522207272847485359/25000000000000000000)
  directionHi := (346088829091389941437/100000000000000000000)

def endpointA : IntegerEndpointWitness 49 where
  qNumerator := 22647
  qDenominator := 43472
  table := BinomialMassData.Q22647_43472.Degree049.table
  base := (-3173340448989750687507587331904128967/6250000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (900614858)
      previous := (450307429)
      next := (450307429)
      square := (5829537300817549292607788731296720000000000000)
      linear := (-297878482987829626245673873386005325000000000000)
      constant := (3767774432128875663484498850613286921922004699200) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22647_43472.Degree049.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 49 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree049.table
  base := (-5077951256629655082774403482211367465807/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (5329082)
      previous := (2664541)
      next := (2664541)
      square := (34494303555133427766909992492880000000000000)
      linear := (-1764538607838703019874701869751175000000000000)
      constant := (22344192417708140790442942093642720257726084433) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree049.checked
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
end ForestUnimodality.Stage99KernelData.Cell107.Kernel049

namespace ForestUnimodality.Stage99KernelData.Cell107.Kernel050
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (86522207272847485359/25000000000000000000)
  centralHi := (346088829091389941437/100000000000000000000)
  directionLo := (21854708601188352649/6250000000000000000)
  directionHi := (69935067523802728477/20000000000000000000)

def endpointA : IntegerEndpointWitness 50 where
  qNumerator := 22647
  qDenominator := 43472
  table := BinomialMassData.Q22647_43472.Degree050.table
  base := (-4761961999658148243420212201416750551877/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (900614858)
      previous := (450307429)
      next := (450307429)
      square := (5829537300817549292607788731296720000000000000)
      linear := (-303952348061974594907326826615563515000000000000)
      constant := (3926866311953895250287486821513351293210244868947) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22647_43472.Degree050.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 50 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree050.table
  base := (-297656678279483852139228111871231927863/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (5329082)
      previous := (2664541)
      next := (2664541)
      square := (34494303555133427766909992492880000000000000)
      linear := (-1800518312025397217258368751872935000000000000)
      constant := (23287615374068715061969546089897393490544260752) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree050.checked
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
end ForestUnimodality.Stage99KernelData.Cell107.Kernel050

namespace ForestUnimodality.Stage99KernelData.Cell107.Kernel051
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (21854708601188352649/6250000000000000000)
  centralHi := (69935067523802728477/20000000000000000000)
  directionLo := (44153179007875001721/12500000000000000000)
  directionHi := (353225432063000013769/100000000000000000000)

def endpointA : IntegerEndpointWitness 51 where
  qNumerator := 22647
  qDenominator := 43472
  table := BinomialMassData.Q22647_43472.Degree051.table
  base := (-884822413474586524620652485713360687823/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (900614858)
      previous := (450307429)
      next := (450307429)
      square := (5829537300817549292607788731296720000000000000)
      linear := (-310026213136119563568979779845121705000000000000)
      constant := (4089288263309865483400420100807075605816946988765) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22647_43472.Degree051.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 51 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree051.table
  base := (-4424601669712574598845276966062886654677/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (5329082)
      previous := (2664541)
      next := (2664541)
      square := (34494303555133427766909992492880000000000000)
      linear := (-1836498016212091414642035633994695000000000000)
      constant := (24250783974418747091015155474297472048037053963) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree051.checked
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
end ForestUnimodality.Stage99KernelData.Cell107.Kernel051

namespace ForestUnimodality.Stage99KernelData.Cell107.Kernel052
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (44153179007875001721/12500000000000000000)
  centralHi := (353225432063000013769/100000000000000000000)
  directionLo := (356740199547534730767/100000000000000000000)
  directionHi := (22296262471720920673/6250000000000000000)

def endpointA : IntegerEndpointWitness 52 where
  qNumerator := 22647
  qDenominator := 43472
  table := BinomialMassData.Q22647_43472.Degree052.table
  base := (-4063940635510492766315170021386197925163/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (5329082)
      previous := (2664541)
      next := (2664541)
      square := (34494303555133427766909992492880000000000000)
      linear := (-1870414663966062320891317947187455000000000000)
      constant := (25177746807829578218752553985954750738430954997) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22647_43472.Degree052.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 52 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree052.table
  base := (-2032190366784740494560522171363898848743/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (5329082)
      previous := (2664541)
      next := (2664541)
      square := (34494303555133427766909992492880000000000000)
      linear := (-1872477720398785612025702516116455000000000000)
      constant := (25233691883911718816347030345455447068776114034) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree052.checked
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
end ForestUnimodality.Stage99KernelData.Cell107.Kernel052

namespace ForestUnimodality.Stage99KernelData.Cell107.Kernel053
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (356740199547534730767/100000000000000000000)
  centralHi := (22296262471720920673/6250000000000000000)
  directionLo := (180110337078647959323/50000000000000000000)
  directionHi := (360220674157295918647/100000000000000000000)

def endpointA : IntegerEndpointWitness 53 where
  qNumerator := 22647
  qDenominator := 43472
  table := BinomialMassData.Q22647_43472.Degree053.table
  base := (-1840787328690362356509688505036851470331/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (900614858)
      previous := (450307429)
      next := (450307429)
      square := (5829537300817549292607788731296720000000000000)
      linear := (-322173943284409500892285686304238085000000000000)
      constant := (4424118216413262459846013704157915100207471397082) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22647_43472.Degree053.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 53 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree053.table
  base := (-920492595919945344655104598014927002961/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (5329082)
      previous := (2664541)
      next := (2664541)
      square := (34494303555133427766909992492880000000000000)
      linear := (-1908457424585479809409369398238215000000000000)
      constant := (26236333583905932437991257562402414894334642236) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree053.checked
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
end ForestUnimodality.Stage99KernelData.Cell107.Kernel053

namespace ForestUnimodality.Stage99KernelData.Cell107.Kernel054
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (180110337078647959323/50000000000000000000)
  centralHi := (360220674157295918647/100000000000000000000)
  directionLo := (363667840491097893357/100000000000000000000)
  directionHi := (181833920245548946679/50000000000000000000)

def endpointA : IntegerEndpointWitness 54 where
  qNumerator := 22647
  qDenominator := 43472
  table := BinomialMassData.Q22647_43472.Degree054.table
  base := (-3277124839586555810082452875180381647207/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (900614858)
      previous := (450307429)
      next := (450307429)
      square := (5829537300817549292607788731296720000000000000)
      linear := (-328247808358554469553938639533796275000000000000)
      constant := (4596524463734061008695813455371650564751351324577) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22647_43472.Degree054.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 54 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree054.table
  base := (-655496155975652257461682311163510003689/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (5329082)
      previous := (2664541)
      next := (2664541)
      square := (34494303555133427766909992492880000000000000)
      linear := (-1944437128772174006793036280359975000000000000)
      constant := (27258704262509644689650245416669903597644303955) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree054.checked
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
end ForestUnimodality.Stage99KernelData.Cell107.Kernel054

namespace ForestUnimodality.Stage99KernelData.Cell107.Kernel055
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (363667840491097893357/100000000000000000000)
  centralHi := (181833920245548946679/50000000000000000000)
  directionLo := (367082636915150865891/100000000000000000000)
  directionHi := (91770659228787716473/25000000000000000000)

def endpointA : IntegerEndpointWitness 55 where
  qNumerator := 22647
  qDenominator := 43472
  table := BinomialMassData.Q22647_43472.Degree055.table
  base := (-1425343903325388761253005858997712979429/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 610090000000000000000000000000000000000000000
      center := (7443098)
      previous := (3721549)
      next := (3721549)
      square := (48177994221632638781882551498320000000000000)
      linear := (-2762989036633879654674310683994665000000000000)
      constant := (39440142472684029226409079147340392057676032278) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22647_43472.Degree055.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 55 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree055.table
  base := (-1425504029748744236603392371595588875989/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (44042)
      previous := (22021)
      next := (22021)
      square := (285076888885400229478594979280000000000000)
      linear := (-16367081264122877720468621177535000000000000)
      constant := (233890906779735799000709465867632984831535942) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree055.checked
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
end ForestUnimodality.Stage99KernelData.Cell107.Kernel055

namespace ForestUnimodality.Stage99KernelData.Cell107.Kernel056
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (367082636915150865891/100000000000000000000)
  centralHi := (91770659228787716473/25000000000000000000)
  directionLo := (370465958546399161567/100000000000000000000)
  directionHi := (11577061204574973799/3125000000000000000)

def endpointA : IntegerEndpointWitness 56 where
  qNumerator := 22647
  qDenominator := 43472
  table := BinomialMassData.Q22647_43472.Degree056.table
  base := (-12011739831811999394833787973317105739/50000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (900614858)
      previous := (450307429)
      next := (450307429)
      square := (5829537300817549292607788731296720000000000000)
      linear := (-340395538506844406877244545992912655000000000000)
      constant := (4951315919689571277691485086958405397542458245800) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22647_43472.Degree056.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 56 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree056.table
  base := (-1201318098084144319604105641827052750891/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (5329082)
      previous := (2664541)
      next := (2664541)
      square := (34494303555133427766909992492880000000000000)
      linear := (-2016396537145562401560370044603495000000000000)
      constant := (29362616289368925308770002558638745017576660458) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree056.checked
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
end ForestUnimodality.Stage99KernelData.Cell107.Kernel056

namespace ForestUnimodality.Stage99KernelData.Cell107.Kernel057
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (370465958546399161567/100000000000000000000)
  centralHi := (11577061204574973799/3125000000000000000)
  directionLo := (373818659992815504103/100000000000000000000)
  directionHi := (46727332499101938013/12500000000000000000)

def endpointA : IntegerEndpointWitness 57 where
  qNumerator := 22647
  qDenominator := 43472
  table := BinomialMassData.Q22647_43472.Degree057.table
  base := (-966089559275161466530299147005550422021/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 204490000000000000000000000000000000000000000
      center := (2494778)
      previous := (1247389)
      next := (1247389)
      square := (16148302772347781973982794269520000000000000)
      linear := (-959749040390552286811350413358645000000000000)
      constant := (14220775513633149882592862117532942623840185142) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22647_43472.Degree057.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 57 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree057.table
  base := (-1932438602752369717031577666929109128749/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (14762)
      previous := (7381)
      next := (7381)
      square := (95552087410341905171495824080000000000000)
      linear := (-5685252746072732961063814201455000000000000)
      constant := (84332827597853499486252920503816577795421371) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree057.checked
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
end ForestUnimodality.Stage99KernelData.Cell107.Kernel057

namespace ForestUnimodality.Stage99KernelData.Cell107.Kernel058
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (373818659992815504103/100000000000000000000)
  centralHi := (46727332499101938013/12500000000000000000)
  directionLo := (75428311574884417137/20000000000000000000)
  directionHi := (188570778937211042843/50000000000000000000)

def endpointA : IntegerEndpointWitness 58 where
  qNumerator := 22647
  qDenominator := 43472
  table := BinomialMassData.Q22647_43472.Degree058.table
  base := (-720122921870539230437482761183602657547/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (900614858)
      previous := (450307429)
      next := (450307429)
      square := (5829537300817549292607788731296720000000000000)
      linear := (-352543268655134344200550452452029035000000000000)
      constant := (5319408884651560501736707496603607484057703048634) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22647_43472.Degree058.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 58 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree058.table
  base := (-1440479514793555563447191698172063468749/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (5329082)
      previous := (2664541)
      next := (2664541)
      square := (34494303555133427766909992492880000000000000)
      linear := (-2088355945518950796327703808847015000000000000)
      constant := (31545400334843805926500166784463696095621574931) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree058.checked
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
end ForestUnimodality.Stage99KernelData.Cell107.Kernel058

namespace ForestUnimodality.Stage99KernelData.Cell107.Kernel059
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (75428311574884417137/20000000000000000000)
  centralHi := (188570778937211042843/50000000000000000000)
  directionLo := (95108858286527366277/25000000000000000000)
  directionHi := (380435433146109465109/100000000000000000000)

def endpointA : IntegerEndpointWitness 59 where
  qNumerator := 22647
  qDenominator := 43472
  table := BinomialMassData.Q22647_43472.Degree059.table
  base := (-926604702839170312882554304957425652317/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (900614858)
      previous := (450307429)
      next := (450307429)
      square := (5829537300817549292607788731296720000000000000)
      linear := (-358617133729279312862203405681587225000000000000)
      constant := (5508442274841920492128505776734977691373712849787) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22647_43472.Degree059.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 59 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree059.table
  base := (-463407592780719337268913575522763396419/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (5329082)
      previous := (2664541)
      next := (2664541)
      square := (34494303555133427766909992492880000000000000)
      linear := (-2124335649705644993711370690968775000000000000)
      constant := (32666362548225934074837198365189125344162043322) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree059.checked
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
end ForestUnimodality.Stage99KernelData.Cell107.Kernel059

namespace ForestUnimodality.Stage99KernelData.Cell107.Kernel060
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (95108858286527366277/25000000000000000000)
  centralHi := (380435433146109465109/100000000000000000000)
  directionLo := (383701033240972371807/100000000000000000000)
  directionHi := (11990657288780386619/3125000000000000000)

def endpointA : IntegerEndpointWitness 60 where
  qNumerator := 22647
  qDenominator := 43472
  table := BinomialMassData.Q22647_43472.Degree060.table
  base := (-195652637220973064459252504579100951867/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (900614858)
      previous := (450307429)
      next := (450307429)
      square := (5829537300817549292607788731296720000000000000)
      linear := (-364690998803424281523856358911145415000000000000)
      constant := (5700799764999028963350215113304037332216666179674) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22647_43472.Degree060.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 60 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree060.table
  base := (-6117108113127358739130291430201460723/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (5329082)
      previous := (2664541)
      next := (2664541)
      square := (34494303555133427766909992492880000000000000)
      linear := (-2160315353892339191095037573090535000000000000)
      constant := (33807035249315430693631332713136491679626152768) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree060.checked
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
end ForestUnimodality.Stage99KernelData.Cell107.Kernel060

namespace ForestUnimodality.Stage99KernelData.Cell107.Kernel061
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (383701033240972371807/100000000000000000000)
  centralHi := (11990657288780386619/3125000000000000000)
  directionLo := (386939074050827342643/100000000000000000000)
  directionHi := (96734768512706835661/25000000000000000000)

def endpointA : IntegerEndpointWitness 61 where
  qNumerator := 22647
  qDenominator := 43472
  table := BinomialMassData.Q22647_43472.Degree061.table
  base := (82804473726817501420750975962099484729/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (900614858)
      previous := (450307429)
      next := (450307429)
      square := (5829537300817549292607788731296720000000000000)
      linear := (-370764863877569250185509312140703605000000000000)
      constant := (5896481034046329397683563785865679177421247237762) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22647_43472.Degree061.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 61 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree061.table
  base := (82719017517162009401564360075528877953/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (5329082)
      previous := (2664541)
      next := (2664541)
      square := (34494303555133427766909992492880000000000000)
      linear := (-2196295058079033388478704455212295000000000000)
      constant := (34967416548946786884847504041056933353835729986) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree061.checked
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
end ForestUnimodality.Stage99KernelData.Cell107.Kernel061

namespace ForestUnimodality.Stage99KernelData.Cell107.Kernel062
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (386939074050827342643/100000000000000000000)
  centralHi := (96734768512706835661/25000000000000000000)
  directionLo := (390150241758778750803/100000000000000000000)
  directionHi := (97537560439694687701/25000000000000000000)

def endpointA : IntegerEndpointWitness 62 where
  qNumerator := 22647
  qDenominator := 43472
  table := BinomialMassData.Q22647_43472.Degree062.table
  base := (744099775878853502434034407251487098657/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (900614858)
      previous := (450307429)
      next := (450307429)
      square := (5829537300817549292607788731296720000000000000)
      linear := (-376838728951714218847162265370261795000000000000)
      constant := (6095485800084220066973219121387835348769637754473) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22647_43472.Degree062.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 62 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree062.table
  base := (743945708863722906397059148351679106807/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (5329082)
      previous := (2664541)
      next := (2664541)
      square := (34494303555133427766909992492880000000000000)
      linear := (-2232274762265727585862371337334055000000000000)
      constant := (36147504788622398106946392270606839695064436567) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree062.checked
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
end ForestUnimodality.Stage99KernelData.Cell107.Kernel062

namespace ForestUnimodality.Stage99KernelData.Cell107.Kernel063
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (390150241758778750803/100000000000000000000)
  centralHi := (97537560439694687701/25000000000000000000)
  directionLo := (196667597268560846753/50000000000000000000)
  directionHi := (393335194537121693507/100000000000000000000)

def endpointA : IntegerEndpointWitness 63 where
  qNumerator := 22647
  qDenominator := 43472
  table := BinomialMassData.Q22647_43472.Degree063.table
  base := (26882673135625776070484324600231459447/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (900614858)
      previous := (450307429)
      next := (450307429)
      square := (5829537300817549292607788731296720000000000000)
      linear := (-382912594025859187508815218599819985000000000000)
      constant := (6297813815413699691933066660498403715211882239150) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22647_43472.Degree063.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 63 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree063.table
  base := (83999671460858441529498782728063419391/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (5329082)
      previous := (2664541)
      next := (2664541)
      square := (34494303555133427766909992492880000000000000)
      linear := (-2268254466452421783246038219455815000000000000)
      constant := (37347298511193275596905599374574637611558692336) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree063.checked
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
end ForestUnimodality.Stage99KernelData.Cell107.Kernel063

namespace ForestUnimodality.Stage99KernelData.Cell107.Kernel064
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (196667597268560846753/50000000000000000000)
  centralHi := (393335194537121693507/100000000000000000000)
  directionLo := (79298912824496459949/20000000000000000000)
  directionHi := (198247282061241149873/50000000000000000000)

def endpointA : IntegerEndpointWitness 64 where
  qNumerator := 22647
  qDenominator := 43472
  table := BinomialMassData.Q22647_43472.Degree064.table
  base := (1965681084085755896124287304920961318851/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (900614858)
      previous := (450307429)
      next := (450307429)
      square := (5829537300817549292607788731296720000000000000)
      linear := (-388986459100004156170468171829378175000000000000)
      constant := (6503464862218295216127910869115711254421315459739) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22647_43472.Degree064.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 64 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree064.table
  base := (1965555806849355770807596242648383101597/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (5329082)
      previous := (2664541)
      next := (2664541)
      square := (34494303555133427766909992492880000000000000)
      linear := (-2304234170639115980629705101577575000000000000)
      constant := (38566796435420776233453820577027444022260858557) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree064.checked
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
end ForestUnimodality.Stage99KernelData.Cell107.Kernel064

namespace ForestUnimodality.Stage99KernelData.Cell107.Kernel065
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (79298912824496459949/20000000000000000000)
  centralHi := (198247282061241149873/50000000000000000000)
  directionLo := (399628957278872734153/100000000000000000000)
  directionHi := (199814478639436367077/50000000000000000000)

def endpointA : IntegerEndpointWitness 65 where
  qNumerator := 22647
  qDenominator := 43472
  table := BinomialMassData.Q22647_43472.Degree065.table
  base := (652179022919401470092365263316811359681/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (5329082)
      previous := (2664541)
      next := (2664541)
      square := (34494303555133427766909992492880000000000000)
      linear := (-2337635054284906064095391272538085000000000000)
      constant := (39718572478188386492160933755915369673008903044) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22647_43472.Degree065.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 65 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree065.table
  base := (1304301544502291003204586279389652764261/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (5329082)
      previous := (2664541)
      next := (2664541)
      square := (34494303555133427766909992492880000000000000)
      linear := (-2340213874825810178013371983699335000000000000)
      constant := (39805997433885797118718346913181313844791369482) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree065.checked
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
end ForestUnimodality.Stage99KernelData.Cell107.Kernel065

namespace ForestUnimodality.Stage99KernelData.Cell107.Kernel066
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (399628957278872734153/100000000000000000000)
  centralHi := (199814478639436367077/50000000000000000000)
  directionLo := (100684739289564430747/25000000000000000000)
  directionHi := (402738957158257722989/100000000000000000000)

def endpointA : IntegerEndpointWitness 66 where
  qNumerator := 22647
  qDenominator := 43472
  table := BinomialMassData.Q22647_43472.Degree066.table
  base := (1636607905898400223245035974883143719867/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 610090000000000000000000000000000000000000000
      center := (7443098)
      previous := (3721549)
      next := (3721549)
      square := (48177994221632638781882551498320000000000000)
      linear := (-3315158588828876805733670068499955000000000000)
      constant := (57229217408169307120899158900764323305410731606) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22647_43472.Degree066.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 66 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree066.table
  base := (1636556930703437853368343708945922957449/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (44042)
      previous := (22021)
      next := (22021)
      square := (285076888885400229478594979280000000000000)
      linear := (-19637963462913259300801974097695000000000000)
      constant := (339379343089154351714892608923048956375278178) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree066.checked
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
end ForestUnimodality.Stage99KernelData.Cell107.Kernel066

namespace ForestUnimodality.Stage99KernelData.Cell107.Kernel067
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (100684739289564430747/25000000000000000000)
  centralHi := (402738957158257722989/100000000000000000000)
  directionLo := (202912562283636600363/50000000000000000000)
  directionHi := (405825124567273200727/100000000000000000000)

def endpointA : IntegerEndpointWitness 67 where
  qNumerator := 22647
  qDenominator := 43472
  table := BinomialMassData.Q22647_43472.Degree067.table
  base := (3959160090816625850336193770356357402821/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (900614858)
      previous := (450307429)
      next := (450307429)
      square := (5829537300817549292607788731296720000000000000)
      linear := (-407208054322439062155427031518052745000000000000)
      constant := (7140354386166375675851874151114610558313433473069) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22647_43472.Degree067.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 67 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree067.table
  base := (3959068095058882568756835663599550481553/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (5329082)
      previous := (2664541)
      next := (2664541)
      square := (34494303555133427766909992492880000000000000)
      linear := (-2412173283199198572780705747942855000000000000)
      constant := (42343504800239781116493999074014156964584716593) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree067.checked
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
end ForestUnimodality.Stage99KernelData.Cell107.Kernel067

namespace ForestUnimodality.Stage99KernelData.Cell107.Kernel068
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (202912562283636600363/50000000000000000000)
  centralHi := (405825124567273200727/100000000000000000000)
  directionLo := (408887999147889728253/100000000000000000000)
  directionHi := (204443999573944864127/50000000000000000000)

def endpointA : IntegerEndpointWitness 68 where
  qNumerator := 22647
  qDenominator := 43472
  table := BinomialMassData.Q22647_43472.Degree068.table
  base := (4666531154650606842501492727047318670843/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (900614858)
      previous := (450307429)
      next := (450307429)
      square := (5829537300817549292607788731296720000000000000)
      linear := (-413281919396584030817079984747610935000000000000)
      constant := (7359295856937617605857010823929429469889524731027) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22647_43472.Degree068.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 68 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree068.table
  base := (933289625481302018145316126518441308297/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (5329082)
      previous := (2664541)
      next := (2664541)
      square := (34494303555133427766909992492880000000000000)
      linear := (-2448152987385892770164372630064615000000000000)
      constant := (43641809521724085481125689511666960173938606285) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree068.checked
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
end ForestUnimodality.Stage99KernelData.Cell107.Kernel068

namespace ForestUnimodality.Stage99KernelData.Cell107.Kernel069
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (408887999147889728253/100000000000000000000)
  centralHi := (204443999573944864127/50000000000000000000)
  directionLo := (411928100479059976331/100000000000000000000)
  directionHi := (102982025119764994083/25000000000000000000)

def endpointA : IntegerEndpointWitness 69 where
  qNumerator := 22647
  qDenominator := 43472
  table := BinomialMassData.Q22647_43472.Degree069.table
  base := (5395313317117127325304995635667282683253/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (900614858)
      previous := (450307429)
      next := (450307429)
      square := (5829537300817549292607788731296720000000000000)
      linear := (-419355784470728999478732937977169125000000000000)
      constant := (7581559602905423191447294607784769582030932455517) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22647_43472.Degree069.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 69 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree069.table
  base := (5395238372125630990143032454912809248303/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (5329082)
      previous := (2664541)
      next := (2664541)
      square := (34494303555133427766909992492880000000000000)
      linear := (-2484132691572586967548039512186375000000000000)
      constant := (44959813997414365447570068260237741420775123343) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree069.checked
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
end ForestUnimodality.Stage99KernelData.Cell107.Kernel069

namespace ForestUnimodality.Stage99KernelData.Cell107.Kernel070
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (411928100479059976331/100000000000000000000)
  centralHi := (102982025119764994083/25000000000000000000)
  directionLo := (103736482276429754313/25000000000000000000)
  directionHi := (414945929105719017253/100000000000000000000)

def endpointA : IntegerEndpointWitness 70 where
  qNumerator := 22647
  qDenominator := 43472
  table := BinomialMassData.Q22647_43472.Degree070.table
  base := (1229098545104129872940349222762267976819/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (900614858)
      previous := (450307429)
      next := (450307429)
      square := (5829537300817549292607788731296720000000000000)
      linear := (-425429649544873968140385891206727315000000000000)
      constant := (7807145521807961081690729504664599818358638974455) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22647_43472.Degree070.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 70 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree070.table
  base := (6145425065966554977395721118685390928041/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (5329082)
      previous := (2664541)
      next := (2664541)
      square := (34494303555133427766909992492880000000000000)
      linear := (-2520112395759281164931706394308135000000000000)
      constant := (46297517626118111294286660379137746561127758921) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree070.checked
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
end ForestUnimodality.Stage99KernelData.Cell107.Kernel070

namespace ForestUnimodality.Stage99KernelData.Cell107.Kernel071
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (103736482276429754313/25000000000000000000)
  centralHi := (414945929105719017253/100000000000000000000)
  directionLo := (104485491875227064173/25000000000000000000)
  directionHi := (417941967500908256693/100000000000000000000)

def endpointA : IntegerEndpointWitness 71 where
  qNumerator := 22647
  qDenominator := 43472
  table := BinomialMassData.Q22647_43472.Degree071.table
  base := (1729264284626085787287297865953177550829/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (900614858)
      previous := (450307429)
      next := (450307429)
      square := (5829537300817549292607788731296720000000000000)
      linear := (-431503514619018936802038844436285505000000000000)
      constant := (8036053523278445678160655163267553916052086807124) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22647_43472.Degree071.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 71 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree071.table
  base := (1383399209545816018906791570875093891109/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (5329082)
      previous := (2664541)
      next := (2664541)
      square := (34494303555133427766909992492880000000000000)
      linear := (-2556092099945975362315373276429895000000000000)
      constant := (47654919876621936999550221832224939881287661145) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree071.checked
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
end ForestUnimodality.Stage99KernelData.Cell107.Kernel071

namespace ForestUnimodality.Stage99KernelData.Cell107.Kernel072
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (104485491875227064173/25000000000000000000)
  centralHi := (417941967500908256693/100000000000000000000)
  directionLo := (420916680966259775281/100000000000000000000)
  directionHi := (210458340483129887641/50000000000000000000)

def endpointA : IntegerEndpointWitness 72 where
  qNumerator := 22647
  qDenominator := 43472
  table := BinomialMassData.Q22647_43472.Degree072.table
  base := (481874733244439258291516250217082561999/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (900614858)
      previous := (450307429)
      next := (450307429)
      square := (5829537300817549292607788731296720000000000000)
      linear := (-437577379693163905463691797665843695000000000000)
      constant := (8268283527411985324077555955942265987188394174576) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22647_43472.Degree072.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 72 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree072.table
  base := (481871285320062770855364803652296194101/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (5329082)
      previous := (2664541)
      next := (2664541)
      square := (34494303555133427766909992492880000000000000)
      linear := (-2592071804132669559699040158551655000000000000)
      constant := (49032020279254966887454899902094615200872412496) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree072.checked
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
end ForestUnimodality.Stage99KernelData.Cell107.Kernel072

namespace ForestUnimodality.Stage99KernelData.Cell107.Kernel073
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (420916680966259775281/100000000000000000000)
  centralHi := (210458340483129887641/50000000000000000000)
  directionLo := (211935259237800008261/50000000000000000000)
  directionHi := (423870518475600016523/100000000000000000000)

def endpointA : IntegerEndpointWitness 73 where
  qNumerator := 22647
  qDenominator := 43472
  table := BinomialMassData.Q22647_43472.Degree073.table
  base := (4262149464487135225028126805276511850927/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (900614858)
      previous := (450307429)
      next := (450307429)
      square := (5829537300817549292607788731296720000000000000)
      linear := (-443651244767308874125344750895401885000000000000)
      constant := (8503835463512037872435980147178226375811195693006) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22647_43472.Degree073.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 73 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree073.table
  base := (8524249105836119245152101455543133318871/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (5329082)
      previous := (2664541)
      next := (2664541)
      square := (34494303555133427766909992492880000000000000)
      linear := (-2628051508319363757082707040673415000000000000)
      constant := (50428818418510153466709381357911854606501604151) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree073.checked
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
end ForestUnimodality.Stage99KernelData.Cell107.Kernel073

namespace ForestUnimodality.Stage99KernelData.Cell107.Kernel074
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (211935259237800008261/50000000000000000000)
  centralHi := (423870518475600016523/100000000000000000000)
  directionLo := (213401956733001768719/50000000000000000000)
  directionHi := (426803913466003537439/100000000000000000000)

def endpointA : IntegerEndpointWitness 74 where
  qNumerator := 22647
  qDenominator := 43472
  table := BinomialMassData.Q22647_43472.Degree074.table
  base := (4679979125831740194413618325746666916143/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (900614858)
      previous := (450307429)
      next := (450307429)
      square := (5829537300817549292607788731296720000000000000)
      linear := (-449725109841453842786997704124960075000000000000)
      constant := (8742709268993026965255783563812234962631646325454) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22647_43472.Degree074.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 74 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree074.table
  base := (4679956624844048412878626239185278008259/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (5329082)
      previous := (2664541)
      next := (2664541)
      square := (34494303555133427766909992492880000000000000)
      linear := (-2664031212506057954466373922795175000000000000)
      constant := (51845313926585337743806957220548774257357522758) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree074.checked
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
end ForestUnimodality.Stage99KernelData.Cell107.Kernel074

namespace ForestUnimodality.Stage99KernelData.Cell107.Kernel075
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (213401956733001768719/50000000000000000000)
  centralHi := (426803913466003537439/100000000000000000000)
  directionLo := (429717284580243172327/100000000000000000000)
  directionHi := (53714660572530396541/12500000000000000000)

def endpointA : IntegerEndpointWitness 75 where
  qNumerator := 22647
  qDenominator := 43472
  table := BinomialMassData.Q22647_43472.Degree075.table
  base := (10216966190437986817962915665082752080529/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (900614858)
      previous := (450307429)
      next := (450307429)
      square := (5829537300817549292607788731296720000000000000)
      linear := (-455798974915598811448650657354518265000000000000)
      constant := (8984904888418855019128088031241510411973400245081) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22647_43472.Degree075.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 75 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree075.table
  base := (5108462769533190591785418421013163226031/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (5329082)
      previous := (2664541)
      next := (2664541)
      square := (34494303555133427766909992492880000000000000)
      linear := (-2700010916692752151850040804916935000000000000)
      constant := (53281506477724633026832213368804176965752520222) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree075.checked
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
end ForestUnimodality.Stage99KernelData.Cell107.Kernel075

namespace ForestUnimodality.Stage99KernelData.Cell107.Kernel076
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (429717284580243172327/100000000000000000000)
  centralHi := (53714660572530396541/12500000000000000000)
  directionLo := (86522207272847485359/20000000000000000000)
  directionHi := (108152759091059356699/25000000000000000000)

def endpointA : IntegerEndpointWitness 76 where
  qNumerator := 22647
  qDenominator := 43472
  table := BinomialMassData.Q22647_43472.Degree076.table
  base := (11095316090035617530229344511321126844121/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 204490000000000000000000000000000000000000000
      center := (2494778)
      previous := (1247389)
      next := (1247389)
      square := (16148302772347781973982794269520000000000000)
      linear := (-1279426149556076953214137425440655000000000000)
      constant := (25569036766370593796359462923100734472835430329) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22647_43472.Degree076.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 76 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree076.table
  base := (11095279365349474458304228330958763530733/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (14762)
      previous := (7381)
      next := (7381)
      square := (95552087410341905171495824080000000000000)
      linear := (-7578921387477690718098913260495000000000000)
      constant := (151627135133675467223683884545586010387218693) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree076.checked
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
end ForestUnimodality.Stage99KernelData.Cell107.Kernel076

namespace ForestUnimodality.Stage99KernelData.Cell107.Kernel077
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (86522207272847485359/20000000000000000000)
  centralHi := (108152759091059356699/25000000000000000000)
  directionLo := (21774277996139241563/5000000000000000000)
  directionHi := (435485559922784831261/100000000000000000000)

def endpointA : IntegerEndpointWitness 77 where
  qNumerator := 22647
  qDenominator := 43472
  table := BinomialMassData.Q22647_43472.Degree077.table
  base := (2998750512310011259105514217084060761857/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 610090000000000000000000000000000000000000000
      center := (7443098)
      previous := (3721549)
      next := (3721549)
      square := (48177994221632638781882551498320000000000000)
      linear := (-3867328141023873956793029453005245000000000000)
      constant := (78341003125227362409507139720828395227080534852) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22647_43472.Degree077.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 77 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree077.table
  base := (5997484434614302849501688222051809289487/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (44042)
      previous := (22021)
      next := (22021)
      square := (285076888885400229478594979280000000000000)
      linear := (-22908845661703640881135327017855000000000000)
      constant := (464570095762326473079763142124536406307009614) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree077.checked
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
end ForestUnimodality.Stage99KernelData.Cell107.Kernel077

namespace ForestUnimodality.Stage99KernelData.Cell107.Kernel078
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (21774277996139241563/5000000000000000000)
  centralHi := (435485559922784831261/100000000000000000000)
  directionLo := (219170616768297249989/50000000000000000000)
  directionHi := (438341233536594499979/100000000000000000000)

def endpointA : IntegerEndpointWitness 78 where
  qNumerator := 22647
  qDenominator := 43472
  table := BinomialMassData.Q22647_43472.Degree078.table
  base := (807251177052845677975323229553615711367/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (5329082)
      previous := (2664541)
      next := (2664541)
      square := (34494303555133427766909992492880000000000000)
      linear := (-2804855444603749807299464597888715000000000000)
      constant := (57582379681954318328318527898707969431211550832) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22647_43472.Degree078.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 78 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree078.table
  base := (807249303323008837609641131518454599/625000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (5329082)
      previous := (2664541)
      next := (2664541)
      square := (34494303555133427766909992492880000000000000)
      linear := (-2807950029252834744001041451282215000000000000)
      constant := (57708263662645057744452118555107571845422704000) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree078.checked
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
end ForestUnimodality.Stage99KernelData.Cell107.Kernel078

namespace ForestUnimodality.Stage99KernelData.Cell107.Kernel079
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (219170616768297249989/50000000000000000000)
  centralHi := (438341233536594499979/100000000000000000000)
  directionLo := (8823568464867377897/2000000000000000000)
  directionHi := (441178423243368894851/100000000000000000000)

def endpointA : IntegerEndpointWitness 79 where
  qNumerator := 22647
  qDenominator := 43472
  table := BinomialMassData.Q22647_43472.Degree079.table
  base := (866147612142130101353241432174657405767/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (900614858)
      previous := (450307429)
      next := (450307429)
      square := (5829537300817549292607788731296720000000000000)
      linear := (-480094435212178686095262470272751025000000000000)
      constant := (9986904602651638905999180362329588319722097716208) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22647_43472.Degree079.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 79 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree079.table
  base := (13858334704464587527504482212735228732369/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (5329082)
      previous := (2664541)
      next := (2664541)
      square := (34494303555133427766909992492880000000000000)
      linear := (-2843929733439528941384708333403975000000000000)
      constant := (59223241807980005850032369899485932526258610289) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree079.checked
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
end ForestUnimodality.Stage99KernelData.Cell107.Kernel079

namespace ForestUnimodality.Stage99KernelData.Cell107.Kernel080
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (8823568464867377897/2000000000000000000)
  centralHi := (441178423243368894851/100000000000000000000)
  directionLo := (88799496677093164771/20000000000000000000)
  directionHi := (27749842711591613991/6250000000000000000)

def endpointA : IntegerEndpointWitness 80 where
  qNumerator := 22647
  qDenominator := 43472
  table := BinomialMassData.Q22647_43472.Degree080.table
  base := (14822026807503846295369320169984479474541/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (900614858)
      previous := (450307429)
      next := (450307429)
      square := (5829537300817549292607788731296720000000000000)
      linear := (-486168300286323654756915423502309215000000000000)
      constant := (10245708656897927656597177397852770381099734896149) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22647_43472.Degree080.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 80 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree080.table
  base := (2964400465513812249805314897010256714811/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (5329082)
      previous := (2664541)
      next := (2664541)
      square := (34494303555133427766909992492880000000000000)
      linear := (-2879909437626223138768375215525735000000000000)
      constant := (60757915844348676808615970925988325117798296455) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree080.checked
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
end ForestUnimodality.Stage99KernelData.Cell107.Kernel080

namespace ForestUnimodality.Stage99KernelData.Cell107.Kernel081
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (88799496677093164771/20000000000000000000)
  centralHi := (27749842711591613991/6250000000000000000)
  directionLo := (223399378563229703683/50000000000000000000)
  directionHi := (446798757126459407367/100000000000000000000)

def endpointA : IntegerEndpointWitness 81 where
  qNumerator := 22647
  qDenominator := 43472
  table := BinomialMassData.Q22647_43472.Degree081.table
  base := (3951752551785866920968054380519464926851/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (900614858)
      previous := (450307429)
      next := (450307429)
      square := (5829537300817549292607788731296720000000000000)
      linear := (-492242165360468623418568376731867405000000000000)
      constant := (10507834301930900830710209390742691688414570286956) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22647_43472.Degree081.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 81 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree081.table
  base := (15806988084513298426081791517170547669871/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (5329082)
      previous := (2664541)
      next := (2664541)
      square := (34494303555133427766909992492880000000000000)
      linear := (-2915889141812917336152042097647495000000000000)
      constant := (62312285612840978874293153083981441692767635151) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree081.checked
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
end ForestUnimodality.Stage99KernelData.Cell107.Kernel081

namespace ForestUnimodality.Stage99KernelData.Cell107.Kernel082
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (223399378563229703683/50000000000000000000)
  centralHi := (446798757126459407367/100000000000000000000)
  directionLo := (224791288469365912961/50000000000000000000)
  directionHi := (449582576938731825923/100000000000000000000)

def endpointA : IntegerEndpointWitness 82 where
  qNumerator := 22647
  qDenominator := 43472
  table := BinomialMassData.Q22647_43472.Degree082.table
  base := (4203327183909752909606717952677219002327/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (900614858)
      previous := (450307429)
      next := (450307429)
      square := (5829537300817549292607788731296720000000000000)
      linear := (-498316030434613592080221329961425595000000000000)
      constant := (10773281513703005364152185054611730757665676484412) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22647_43472.Degree082.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 82 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree082.table
  base := (16813288742430556408545342109022223748719/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (5329082)
      previous := (2664541)
      next := (2664541)
      square := (34494303555133427766909992492880000000000000)
      linear := (-2951868845999611533535708979769255000000000000)
      constant := (63886350972242059861363815369054989755567794639) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree082.checked
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
end ForestUnimodality.Stage99KernelData.Cell107.Kernel082

namespace ForestUnimodality.Stage99KernelData.Cell107.Kernel083
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (224791288469365912961/50000000000000000000)
  centralHi := (449582576938731825923/100000000000000000000)
  directionLo := (452349265064057092679/100000000000000000000)
  directionHi := (11308731626601427317/2500000000000000000)

def endpointA : IntegerEndpointWitness 83 where
  qNumerator := 22647
  qDenominator := 43472
  table := BinomialMassData.Q22647_43472.Degree083.table
  base := (2230114937091426569634836330249419513977/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (900614858)
      previous := (450307429)
      next := (450307429)
      square := (5829537300817549292607788731296720000000000000)
      linear := (-504389895508758560741874283190983785000000000000)
      constant := (11042050270833799067592637014449526337654119663624) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22647_43472.Degree083.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 83 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree083.table
  base := (2230112678411692872541894126539040067267/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (5329082)
      previous := (2664541)
      next := (2664541)
      square := (34494303555133427766909992492880000000000000)
      linear := (-2987848550186305730919375861891015000000000000)
      constant := (65480111797011533618537276739650239473426318616) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree083.checked
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
end ForestUnimodality.Stage99KernelData.Cell107.Kernel083

namespace ForestUnimodality.Stage99KernelData.Cell107.Kernel084
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (452349265064057092679/100000000000000000000)
  centralHi := (11308731626601427317/2500000000000000000)
  directionLo := (56887391743622884941/12500000000000000000)
  directionHi := (455099133948983079529/100000000000000000000)

def endpointA : IntegerEndpointWitness 84 where
  qNumerator := 22647
  qDenominator := 43472
  table := BinomialMassData.Q22647_43472.Degree084.table
  base := (18889839914395986445723566593584721573311/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (900614858)
      previous := (450307429)
      next := (450307429)
      square := (5829537300817549292607788731296720000000000000)
      linear := (-510463760582903529403527236420541975000000000000)
      constant := (11314140554306838457590213273998711104944401826679) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22647_43472.Degree084.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 84 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree084.table
  base := (4722455895776158387460342153482483148871/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (5329082)
      previous := (2664541)
      next := (2664541)
      square := (34494303555133427766909992492880000000000000)
      linear := (-3023828254372999928303042744012775000000000000)
      constant := (67093567975500867906027427092730893385703336604) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree084.checked
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
end ForestUnimodality.Stage99KernelData.Cell107.Kernel084

namespace ForestUnimodality.Stage99KernelData.Cell107.Kernel085
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (56887391743622884941/12500000000000000000)
  centralHi := (455099133948983079529/100000000000000000000)
  directionLo := (228916243328338489551/50000000000000000000)
  directionHi := (457832486656676979103/100000000000000000000)

def endpointA : IntegerEndpointWitness 85 where
  qNumerator := 22647
  qDenominator := 43472
  table := BinomialMassData.Q22647_43472.Degree085.table
  base := (998003384829697242170165908951992941719/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (900614858)
      previous := (450307429)
      next := (450307429)
      square := (5829537300817549292607788731296720000000000000)
      linear := (-516537625657048498065180189650100165000000000000)
      constant := (11589552347202089206273947512248253994337829419820) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22647_43472.Degree085.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 85 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree085.table
  base := (1247503308491974737704538562939620932473/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (5329082)
      previous := (2664541)
      next := (2664541)
      square := (34494303555133427766909992492880000000000000)
      linear := (-3059807958559694125686709626134535000000000000)
      constant := (68726719408379808024135545512034224311221649808) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree085.checked
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
end ForestUnimodality.Stage99KernelData.Cell107.Kernel085

namespace ForestUnimodality.Stage99KernelData.Cell107.Kernel086
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (228916243328338489551/50000000000000000000)
  centralHi := (457832486656676979103/100000000000000000000)
  directionLo := (28784351078548181013/6250000000000000000)
  directionHi := (460549617256770896209/100000000000000000000)

def endpointA : IntegerEndpointWitness 86 where
  qNumerator := 22647
  qDenominator := 43472
  table := BinomialMassData.Q22647_43472.Degree086.table
  base := (21051600803251111877094172776484691894447/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (900614858)
      previous := (450307429)
      next := (450307429)
      square := (5829537300817549292607788731296720000000000000)
      linear := (-522611490731193466726833142879658355000000000000)
      constant := (11868285634459542180747525540587702465827386359783) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22647_43472.Degree086.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 86 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree086.table
  base := (21051587461786934602389995446846597764839/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (5329082)
      previous := (2664541)
      next := (2664541)
      square := (34494303555133427766909992492880000000000000)
      linear := (-3095787662746388323070376508256295000000000000)
      constant := (70379566007246418777728218486765596236965932359) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree086.checked
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
end ForestUnimodality.Stage99KernelData.Cell107.Kernel086

namespace ForestUnimodality.Stage99KernelData.Cell107.Kernel087
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (28784351078548181013/6250000000000000000)
  centralHi := (460549617256770896209/100000000000000000000)
  directionLo := (463250811194627079241/100000000000000000000)
  directionHi := (231625405597313539621/50000000000000000000)

def endpointA : IntegerEndpointWitness 87 where
  qNumerator := 22647
  qDenominator := 43472
  table := BinomialMassData.Q22647_43472.Degree087.table
  base := (22164437417953016162467627143405911410569/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (900614858)
      previous := (450307429)
      next := (450307429)
      square := (5829537300817549292607788731296720000000000000)
      linear := (-528685355805338435388486096109216545000000000000)
      constant := (12150340402670264092363881142844034686158935898641) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22647_43472.Degree087.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 87 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree087.table
  base := (22164425359102607820546580274271801537399/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (5329082)
      previous := (2664541)
      next := (2664541)
      square := (34494303555133427766909992492880000000000000)
      linear := (-3131767366933082520454043390378055000000000000)
      constant := (72052107693398543938671381744572031562955125719) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree087.checked
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
end ForestUnimodality.Stage99KernelData.Cell107.Kernel087

namespace ForestUnimodality.Stage99KernelData.Cell107.Kernel088
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (463250811194627079241/100000000000000000000)
  centralHi := (231625405597313539621/50000000000000000000)
  directionLo := (93187269128267062101/20000000000000000000)
  directionHi := (232968172820667655253/50000000000000000000)

def endpointA : IntegerEndpointWitness 88 where
  qNumerator := 22647
  qDenominator := 43472
  table := BinomialMassData.Q22647_43472.Degree088.table
  base := (5824643980727438498430894026396243409143/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 610090000000000000000000000000000000000000000
      center := (7443098)
      previous := (3721549)
      next := (3721549)
      square := (48177994221632638781882551498320000000000000)
      linear := (-4419497693218871107852388837510535000000000000)
      constant := (102774517685054428831945191127370321156593621148) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22647_43472.Degree088.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 88 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree088.table
  base := (23298565023255795720561645616068527995281/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (44042)
      previous := (22021)
      next := (22021)
      square := (285076888885400229478594979280000000000000)
      linear := (-26179727860494022461468679938015000000000000)
      constant := (609457391708655165107646644616400738606296441) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree088.checked
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
end ForestUnimodality.Stage99KernelData.Cell107.Kernel088

namespace ForestUnimodality.Stage99KernelData.Cell107.Kernel089
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (93187269128267062101/20000000000000000000)
  centralHi := (232968172820667655253/50000000000000000000)
  directionLo := (234303244912828590539/50000000000000000000)
  directionHi := (468606489825657181079/100000000000000000000)

def endpointA : IntegerEndpointWitness 89 where
  qNumerator := 22647
  qDenominator := 43472
  table := BinomialMassData.Q22647_43472.Degree089.table
  base := (24454014876799834056266213927742074592389/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (900614858)
      previous := (450307429)
      next := (450307429)
      square := (5829537300817549292607788731296720000000000000)
      linear := (-540833085953628372711792002568332925000000000000)
      constant := (12724414335483544043154913254326479034310654320621) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22647_43472.Degree089.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 89 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree089.table
  base := (24454005024856961627933038158001712257819/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (5329082)
      previous := (2664541)
      next := (2664541)
      square := (34494303555133427766909992492880000000000000)
      linear := (-3203726775306470915221377154621575000000000000)
      constant := (75456276054855447544310876689883867793133791739) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree089.checked
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
end ForestUnimodality.Stage99KernelData.Cell107.Kernel089

namespace ForestUnimodality.Stage99KernelData.Cell107.Kernel090
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (234303244912828590539/50000000000000000000)
  centralHi := (468606489825657181079/100000000000000000000)
  directionLo := (471261505349042494791/100000000000000000000)
  directionHi := (58907688168630311849/12500000000000000000)

def endpointA : IntegerEndpointWitness 90 where
  qNumerator := 22647
  qDenominator := 43472
  table := BinomialMassData.Q22647_43472.Degree090.table
  base := (12815376497575380898525543168007161022889/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (900614858)
      previous := (450307429)
      next := (450307429)
      square := (5829537300817549292607788731296720000000000000)
      linear := (-546906951027773341373444955797891115000000000000)
      constant := (13016433479964048282989927144181958964991595270242) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22647_43472.Degree090.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 90 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree090.table
  base := (25630744090199761064500283971520097124611/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (5329082)
      previous := (2664541)
      next := (2664541)
      square := (34494303555133427766909992492880000000000000)
      linear := (-3239706479493165112605044036743335000000000000)
      constant := (77187902612086294804377752156797119362500133091) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree090.checked
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
end ForestUnimodality.Stage99KernelData.Cell107.Kernel090

namespace ForestUnimodality.Stage99KernelData.Cell107.Kernel091
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (471261505349042494791/100000000000000000000)
  centralHi := (58907688168630311849/12500000000000000000)
  directionLo := (118475411621190271319/25000000000000000000)
  directionHi := (473901646484761085277/100000000000000000000)

def endpointA : IntegerEndpointWitness 91 where
  qNumerator := 22647
  qDenominator := 43472
  table := BinomialMassData.Q22647_43472.Degree091.table
  base := (26828789132956387347100186849194013087573/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (5329082)
      previous := (2664541)
      next := (2664541)
      square := (34494303555133427766909992492880000000000000)
      linear := (-3272075834922593550503537923239345000000000000)
      constant := (78767893875032907125977963391073352435678276213) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22647_43472.Degree091.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 91 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree091.table
  base := (1073151243359776814769074998244660077929/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (5329082)
      previous := (2664541)
      next := (2664541)
      square := (34494303555133427766909992492880000000000000)
      linear := (-3275686183679859309988710918865095000000000000)
      constant := (78939224018849224154938134688985989921600416225) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree091.checked
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
end ForestUnimodality.Stage99KernelData.Cell107.Kernel091

namespace ForestUnimodality.Stage99KernelData.Cell107.Kernel092
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (118475411621190271319/25000000000000000000)
  centralHi := (473901646484761085277/100000000000000000000)
  directionLo := (238263580231059090757/50000000000000000000)
  directionHi := (95305432092423636303/20000000000000000000)

def endpointA : IntegerEndpointWitness 92 where
  qNumerator := 22647
  qDenominator := 43472
  table := BinomialMassData.Q22647_43472.Degree092.table
  base := (14024061134633935164038714616751004681901/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (900614858)
      previous := (450307429)
      next := (450307429)
      square := (5829537300817549292607788731296720000000000000)
      linear := (-559054681176063278696750862257007495000000000000)
      constant := (13610436082696347902936288600565359418552419742378) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22647_43472.Degree092.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 92 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree092.table
  base := (7012028748515714204553600893587315477451/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (5329082)
      previous := (2664541)
      next := (2664541)
      square := (34494303555133427766909992492880000000000000)
      linear := (-3311665887866553507372377800986855000000000000)
      constant := (80710240230931284764529417946807490109482148524) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree092.checked
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
end ForestUnimodality.Stage99KernelData.Cell107.Kernel092

namespace ForestUnimodality.Stage99KernelData.Cell107.Kernel093
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (238263580231059090757/50000000000000000000)
  centralHi := (95305432092423636303/20000000000000000000)
  directionLo := (479138287736652486171/100000000000000000000)
  directionHi := (119784571934163121543/25000000000000000000)

def endpointA : IntegerEndpointWitness 93 where
  qNumerator := 22647
  qDenominator := 43472
  table := BinomialMassData.Q22647_43472.Degree093.table
  base := (29288751493527235788374891062284632142901/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (900614858)
      previous := (450307429)
      next := (450307429)
      square := (5829537300817549292607788731296720000000000000)
      linear := (-565128546250208247358403815486565685000000000000)
      constant := (13912419526689588068175425130145194107186155900189) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22647_43472.Degree093.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 93 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree093.table
  base := (14644372458882887693806544224256921145663/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (5329082)
      previous := (2664541)
      next := (2664541)
      square := (34494303555133427766909992492880000000000000)
      linear := (-3347645592053247704756044683108615000000000000)
      constant := (82500951208904289587214819629902108145127411006) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree093.checked
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
end ForestUnimodality.Stage99KernelData.Cell107.Kernel093

namespace ForestUnimodality.Stage99KernelData.Cell107.Kernel094
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (479138287736652486171/100000000000000000000)
  centralHi := (119784571934163121543/25000000000000000000)
  directionLo := (48173526224715276803/10000000000000000000)
  directionHi := (481735262247152768031/100000000000000000000)

def endpointA : IntegerEndpointWitness 94 where
  qNumerator := 22647
  qDenominator := 43472
  table := BinomialMassData.Q22647_43472.Degree094.table
  base := (30550675993440534650353117014151567037199/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (900614858)
      previous := (450307429)
      next := (450307429)
      square := (5829537300817549292607788731296720000000000000)
      linear := (-571202411324353216020056768716123875000000000000)
      constant := (14217724390863855573755083032736873722983069328711) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22647_43472.Degree094.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 94 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree094.table
  base := (30550670049959876878594332888986936104579/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (5329082)
      previous := (2664541)
      next := (2664541)
      square := (34494303555133427766909992492880000000000000)
      linear := (-3383625296239941902139711565230375000000000000)
      constant := (84311356917598774170690307806270408355984115299) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree094.checked
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
end ForestUnimodality.Stage99KernelData.Cell107.Kernel094

namespace ForestUnimodality.Stage99KernelData.Cell107.Kernel095
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (48173526224715276803/10000000000000000000)
  centralHi := (481735262247152768031/100000000000000000000)
  directionLo := (4843183116602705037/1000000000000000000)
  directionHi := (484318311660270503701/100000000000000000000)

def endpointA : IntegerEndpointWitness 95 where
  qNumerator := 22647
  qDenominator := 43472
  table := BinomialMassData.Q22647_43472.Degree095.table
  base := (1591694752210605978713474532667351028169/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 204490000000000000000000000000000000000000000
      center := (2494778)
      previous := (1247389)
      next := (1247389)
      square := (16148302772347781973982794269520000000000000)
      linear := (-1599103258721601619616924437522665000000000000)
      constant := (40239198531492089873132047303930155723500557620) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22647_43472.Degree095.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 95 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree095.table
  base := (397923620903846076872253293037551680247/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (14762)
      previous := (7381)
      next := (7381)
      square := (95552087410341905171495824080000000000000)
      linear := (-9472590028882648475134012319535000000000000)
      constant := (238618995361875455023006525167928500264790960) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree095.checked
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
end ForestUnimodality.Stage99KernelData.Cell107.Kernel095

namespace ForestUnimodality.Stage99KernelData.Cell107.Kernel096
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (4843183116602705037/1000000000000000000)
  centralHi := (484318311660270503701/100000000000000000000)
  directionLo := (486887657603452474813/100000000000000000000)
  directionHi := (243443828801726237407/50000000000000000000)

def endpointA : IntegerEndpointWitness 96 where
  qNumerator := 22647
  qDenominator := 43472
  table := BinomialMassData.Q22647_43472.Degree096.table
  base := (33138407998982968986465070579653055988911/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (900614858)
      previous := (450307429)
      next := (450307429)
      square := (5829537300817549292607788731296720000000000000)
      linear := (-583350141472643153343362675175240255000000000000)
      constant := (14838298358928783811802512901028738158432124015079) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22647_43472.Degree096.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 96 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree096.table
  base := (33138403143783821708592647175306916666567/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (5329082)
      previous := (2664541)
      next := (2664541)
      square := (34494303555133427766909992492880000000000000)
      linear := (-3455584704613330296907045329473895000000000000)
      constant := (87991252405018455176082653175112421426912313127) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree096.checked
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
end ForestUnimodality.Stage99KernelData.Cell107.Kernel096

namespace ForestUnimodality.Stage99KernelData.Cell107.Kernel097
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (486887657603452474813/100000000000000000000)
  centralHi := (243443828801726237407/50000000000000000000)
  directionLo := (489443515886867821189/100000000000000000000)
  directionHi := (48944351588686782119/10000000000000000000)

def endpointA : IntegerEndpointWitness 97 where
  qNumerator := 22647
  qDenominator := 43472
  table := BinomialMassData.Q22647_43472.Degree097.table
  base := (34464214280334740415987495312278894934151/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (900614858)
      previous := (450307429)
      next := (450307429)
      square := (5829537300817549292607788731296720000000000000)
      linear := (-589424006546788122005015628404798445000000000000)
      constant := (15153567453781720082207564258455360233350551821439) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22647_43472.Degree097.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 97 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree097.table
  base := (34464209892240179461057598096817909445177/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (5329082)
      previous := (2664541)
      next := (2664541)
      square := (34494303555133427766909992492880000000000000)
      linear := (-3491564408800024494290712211595655000000000000)
      constant := (89860742130751020574093327260852218102474776537) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree097.checked
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
end ForestUnimodality.Stage99KernelData.Cell107.Kernel097

namespace ForestUnimodality.Stage99KernelData.Cell107.Kernel098
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (489443515886867821189/100000000000000000000)
  centralHi := (48944351588686782119/10000000000000000000)
  directionLo := (491986096714958495011/100000000000000000000)
  directionHi := (122996524178739623753/25000000000000000000)

def endpointA : IntegerEndpointWitness 98 where
  qNumerator := 22647
  qDenominator := 43472
  table := BinomialMassData.Q22647_43472.Degree098.table
  base := (17905656686368828390611473577125140783633/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (900614858)
      previous := (450307429)
      next := (450307429)
      square := (5829537300817549292607788731296720000000000000)
      linear := (-595497871620933090666668581634356635000000000000)
      constant := (15472157950621766558849189683129813453679617098674) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22647_43472.Degree098.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 98 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree098.table
  base := (17905654703454420041046891098021040415003/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (5329082)
      previous := (2664541)
      next := (2664541)
      square := (34494303555133427766909992492880000000000000)
      linear := (-3527544112986718691674379093717415000000000000)
      constant := (91749926480523881973298500091885464132735492086) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree098.checked
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
end ForestUnimodality.Stage99KernelData.Cell107.Kernel098

namespace ForestUnimodality.Stage99KernelData.Cell107.Kernel099
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (491986096714958495011/100000000000000000000)
  centralHi := (122996524178739623753/25000000000000000000)
  directionLo := (123628901222050004819/25000000000000000000)
  directionHi := (494515604888200019277/100000000000000000000)

def endpointA : IntegerEndpointWitness 99 where
  qNumerator := 22647
  qDenominator := 43472
  table := BinomialMassData.Q22647_43472.Degree099.table
  base := (18589852407917363208998757396290300214309/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 610090000000000000000000000000000000000000000
      center := (7443098)
      previous := (3721549)
      next := (3721549)
      square := (48177994221632638781882551498320000000000000)
      linear := (-4971667245413868258911748222015825000000000000)
      constant := (130529502859921710392480985539351436101549555562) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 99 interval.damping) (curvature.centralUpper 99 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22647_43472.Degree099.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 99 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree099.table
  base := (18589850615867915249938688153105623227539/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (44042)
      previous := (22021)
      next := (22021)
      square := (285076888885400229478594979280000000000000)
      linear := (-29450610059284404041802032858175000000000000)
      constant := (774039714334017733685519299574087259970283158) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 99 interval.damping) (curvature.centralUpper 99 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree099.checked
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
end ForestUnimodality.Stage99KernelData.Cell107.Kernel099

namespace ForestUnimodality.Stage99KernelData.Cell107.Kernel100
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (123628901222050004819/25000000000000000000)
  centralHi := (494515604888200019277/100000000000000000000)
  directionLo := (19881289599824824867/4000000000000000000)
  directionHi := (124258059998905155419/25000000000000000000)

def endpointA : IntegerEndpointWitness 100 where
  qNumerator := 22647
  qDenominator := 43472
  table := BinomialMassData.Q22647_43472.Degree100.table
  base := (4821173524808428697734047052611597729727/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (900614858)
      previous := (450307429)
      next := (450307429)
      square := (5829537300817549292607788731296720000000000000)
      linear := (-607645601769223027989974488093473015000000000000)
      constant := (16119303137032792492268888322220674881234341277624) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 100 interval.damping) (curvature.centralUpper 100 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22647_43472.Degree100.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 100 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree100.table
  base := (1928469247972571719304251464010748092851/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (5329082)
      previous := (2664541)
      next := (2664541)
      square := (34494303555133427766909992492880000000000000)
      linear := (-3599503521360107086441712857960935000000000000)
      constant := (95587378974637863503103840429132569748876490620) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 100 interval.damping) (curvature.centralUpper 100 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree100.checked
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
end ForestUnimodality.Stage99KernelData.Cell107.Kernel100

namespace ForestUnimodality.Stage99KernelData.Cell107.Kernel101
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (19881289599824824867/4000000000000000000)
  centralHi := (124258059998905155419/25000000000000000000)
  directionLo := (499536196598590917691/100000000000000000000)
  directionHi := (124884049149647729423/25000000000000000000)

def endpointA : IntegerEndpointWitness 101 where
  qNumerator := 22647
  qDenominator := 43472
  table := BinomialMassData.Q22647_43472.Degree101.table
  base := (9995090788339774062154198525578880976231/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (900614858)
      previous := (450307429)
      next := (450307429)
      square := (5829537300817549292607788731296720000000000000)
      linear := (-613719466843367996651627441323031205000000000000)
      constant := (16447857820857294097442753435021606460422776506236) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 101 interval.damping) (curvature.centralUpper 101 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22647_43472.Degree101.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 101 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree101.table
  base := (7996072045258755732613292784048145427769/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (5329082)
      previous := (2664541)
      next := (2664541)
      square := (34494303555133427766909992492880000000000000)
      linear := (-3635483225546801283825379740082695000000000000)
      constant := (97535647085299552776861673875611850202151888445) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 101 interval.damping) (curvature.centralUpper 101 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree101.checked
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
end ForestUnimodality.Stage99KernelData.Cell107.Kernel101

namespace ForestUnimodality.Stage99KernelData.Cell107.Kernel102
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (499536196598590917691/100000000000000000000)
  centralHi := (124884049149647729423/25000000000000000000)
  directionLo := (100405532881272621049/20000000000000000000)
  directionHi := (251013832203181552623/50000000000000000000)

def endpointA : IntegerEndpointWitness 102 where
  qNumerator := 22647
  qDenominator := 43472
  table := BinomialMassData.Q22647_43472.Degree102.table
  base := (8282525870476389535983620782698002440919/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (900614858)
      previous := (450307429)
      next := (450307429)
      square := (5829537300817549292607788731296720000000000000)
      linear := (-619793331917512965313280394552589395000000000000)
      constant := (16779733895101763306993262793754994558830406498955) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 102 interval.damping) (curvature.centralUpper 102 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22647_43472.Degree102.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 102 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree102.table
  base := (5176578338414014674688636036087764739087/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (5329082)
      previous := (2664541)
      next := (2664541)
      square := (34494303555133427766909992492880000000000000)
      linear := (-3671462929733495481209046622204455000000000000)
      constant := (99503609752207040064108308259476687212544473976) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 102 interval.damping) (curvature.centralUpper 102 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree102.checked
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
end ForestUnimodality.Stage99KernelData.Cell107.Kernel102

namespace ForestUnimodality.Stage99KernelData.Cell107.Kernel103
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (100405532881272621049/20000000000000000000)
  centralHi := (251013832203181552623/50000000000000000000)
  directionLo := (126126707110951970519/25000000000000000000)
  directionHi := (504506828443807882077/100000000000000000000)

def endpointA : IntegerEndpointWitness 103 where
  qNumerator := 22647
  qDenominator := 43472
  table := BinomialMassData.Q22647_43472.Degree103.table
  base := (8573237300468469398942449379626345502779/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (900614858)
      previous := (450307429)
      next := (450307429)
      square := (5829537300817549292607788731296720000000000000)
      linear := (-625867196991657933974933347782147585000000000000)
      constant := (17114931357601818599230719100504299746231321626655) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 103 interval.damping) (curvature.centralUpper 103 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22647_43472.Degree103.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 103 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree103.table
  base := (857323682243695196976386420213054094611/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (5329082)
      previous := (2664541)
      next := (2664541)
      square := (34494303555133427766909992492880000000000000)
      linear := (-3707442633920189678592713504326215000000000000)
      constant := (101491266962678783591603875352688045795335154550) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 103 interval.damping) (curvature.centralUpper 103 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree103.checked
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
end ForestUnimodality.Stage99KernelData.Cell107.Kernel103

namespace ForestUnimodality.Stage99KernelData.Cell107.Kernel104
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (126126707110951970519/25000000000000000000)
  centralHi := (504506828443807882077/100000000000000000000)
  directionLo := (253486934605884400903/50000000000000000000)
  directionHi := (506973869211768801807/100000000000000000000)

def endpointA : IntegerEndpointWitness 104 where
  qNumerator := 22647
  qDenominator := 43472
  table := BinomialMassData.Q22647_43472.Degree104.table
  base := (44341034341226349189695753345708559680741/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (5329082)
      previous := (2664541)
      next := (2664541)
      square := (34494303555133427766909992492880000000000000)
      linear := (-3739296225241437293707611248589975000000000000)
      constant := (103274853292445264573370596732885028095414447621) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 104 interval.damping) (curvature.centralUpper 104 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22647_43472.Degree104.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 104 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree104.table
  base := (2771314511343380780908786013602632639381/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (5329082)
      previous := (2664541)
      next := (2664541)
      square := (34494303555133427766909992492880000000000000)
      linear := (-3743422338106883875976380386447975000000000000)
      constant := (103498618705383162583073949027926145541132823376) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 104 interval.damping) (curvature.centralUpper 104 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree104.checked
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
end ForestUnimodality.Stage99KernelData.Cell107.Kernel104

namespace ForestUnimodality.Stage99KernelData.Cell107.Kernel105
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (253486934605884400903/50000000000000000000)
  centralHi := (506973869211768801807/100000000000000000000)
  directionLo := (509428962840427359401/100000000000000000000)
  directionHi := (254714481420213679701/50000000000000000000)

def endpointA : IntegerEndpointWitness 105 where
  qNumerator := 22647
  qDenominator := 43472
  table := BinomialMassData.Q22647_43472.Degree105.table
  base := (45837172634854286748163014822437649960057/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (900614858)
      previous := (450307429)
      next := (450307429)
      square := (5829537300817549292607788731296720000000000000)
      linear := (-638014927139947871298239254241263965000000000000)
      constant := (17795290439837321500401268247557468894580987219073) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 105 interval.damping) (curvature.centralUpper 105 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22647_43472.Degree105.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 105 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree105.table
  base := (45837170683407753024792658389993180103537/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (5329082)
      previous := (2664541)
      next := (2664541)
      square := (34494303555133427766909992492880000000000000)
      linear := (-3779402042293578073360047268569735000000000000)
      constant := (105525664970193507620460652464695967100102599697) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 105 interval.damping) (curvature.centralUpper 105 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree105.checked
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
end ForestUnimodality.Stage99KernelData.Cell107.Kernel105

namespace ForestUnimodality.Stage99KernelData.Cell107.Kernel106
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (509428962840427359401/100000000000000000000)
  centralHi := (254714481420213679701/50000000000000000000)
  directionLo := (255936140618023786429/50000000000000000000)
  directionHi := (511872281236047572859/100000000000000000000)

def endpointA : IntegerEndpointWitness 106 where
  qNumerator := 22647
  qDenominator := 43472
  table := BinomialMassData.Q22647_43472.Degree106.table
  base := (47354601173898984602046288757406039881297/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (900614858)
      previous := (450307429)
      next := (450307429)
      square := (5829537300817549292607788731296720000000000000)
      linear := (-644088792214092839959892207470822155000000000000)
      constant := (18140452056298762125264574165916428914916283889433) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 106 interval.damping) (curvature.centralUpper 106 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22647_43472.Degree106.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 106 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree106.table
  base := (9470919882144167698046000223589005222091/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (5329082)
      previous := (2664541)
      next := (2664541)
      square := (34494303555133427766909992492880000000000000)
      linear := (-3815381746480272270743714150691495000000000000)
      constant := (107572405748058901338033621976652746685530784855) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 106 interval.damping) (curvature.centralUpper 106 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree106.checked
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
end ForestUnimodality.Stage99KernelData.Cell107.Kernel106

namespace ForestUnimodality.Stage99KernelData.Cell107.Kernel107
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (255936140618023786429/50000000000000000000)
  centralHi := (511872281236047572859/100000000000000000000)
  directionLo := (514303992221446051751/100000000000000000000)
  directionHi := (64287999027680756469/12500000000000000000)

def endpointA : IntegerEndpointWitness 107 where
  qNumerator := 22647
  qDenominator := 43472
  table := BinomialMassData.Q22647_43472.Degree107.table
  base := (48893319771227364825920498768292348886191/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (900614858)
      previous := (450307429)
      next := (450307429)
      square := (5829537300817549292607788731296720000000000000)
      linear := (-650162657288237808621545160700380345000000000000)
      constant := (18488935054426138551400125326248355351246912832999) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 107 interval.damping) (curvature.centralUpper 107 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22647_43472.Degree107.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 107 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree107.table
  base := (48893318178219166594102488721214091338661/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (5329082)
      previous := (2664541)
      next := (2664541)
      square := (34494303555133427766909992492880000000000000)
      linear := (-3851361450666966468127381032813255000000000000)
      constant := (109638841030889003038888515760766017723764051141) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 107 interval.damping) (curvature.centralUpper 107 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree107.checked
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
end ForestUnimodality.Stage99KernelData.Cell107.Kernel107

namespace ForestUnimodality.Stage99KernelData.Cell107.Kernel108
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (514303992221446051751/100000000000000000000)
  centralHi := (64287999027680756469/12500000000000000000)
  directionLo := (20668970386820494999/4000000000000000000)
  directionHi := (8073816557351755859/1562500000000000000)

def endpointA : IntegerEndpointWitness 108 where
  qNumerator := 22647
  qDenominator := 43472
  table := BinomialMassData.Q22647_43472.Degree108.table
  base := (25226664129764880826506259653464492870613/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (900614858)
      previous := (450307429)
      next := (450307429)
      square := (5829537300817549292607788731296720000000000000)
      linear := (-656236522362382777283198113929938535000000000000)
      constant := (18840739432984355935557349272948501258171461301114) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 108 interval.damping) (curvature.centralUpper 108 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22647_43472.Degree108.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 108 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree108.table
  base := (12613331705082035684031778820954056816743/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (5329082)
      previous := (2664541)
      next := (2664541)
      square := (34494303555133427766909992492880000000000000)
      linear := (-3887341154853660665511047914935015000000000000)
      constant := (111724970811451348856290371835619676623248603932) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 108 interval.damping) (curvature.centralUpper 108 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree108.checked
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
end ForestUnimodality.Stage99KernelData.Cell107.Kernel108

namespace ForestUnimodality.Stage99KernelData.Cell107.Kernel109
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (20668970386820494999/4000000000000000000)
  centralHi := (8073816557351755859/1562500000000000000)
  directionLo := (259566621818542456077/50000000000000000000)
  directionHi := (103826648727416982431/20000000000000000000)

def endpointA : IntegerEndpointWitness 109 where
  qNumerator := 22647
  qDenominator := 43472
  table := BinomialMassData.Q22647_43472.Degree109.table
  base := (52034626489205295034571718598431907611557/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (900614858)
      previous := (450307429)
      next := (450307429)
      square := (5829537300817549292607788731296720000000000000)
      linear := (-662310387436527745944851067159496725000000000000)
      constant := (19195865190869047266738044503448444666803291202573) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 109 interval.damping) (curvature.centralUpper 109 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22647_43472.Degree109.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 109 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree109.table
  base := (52034625189015789303649949176806119220873/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (5329082)
      previous := (2664541)
      next := (2664541)
      square := (34494303555133427766909992492880000000000000)
      linear := (-3923320859040354862894714797056775000000000000)
      constant := (113830795083279753976140853813729763093686953513) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 109 interval.damping) (curvature.centralUpper 109 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree109.checked
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
end ForestUnimodality.Stage99KernelData.Cell107.Kernel109

namespace ForestUnimodality.Stage99KernelData.Cell107.Kernel110
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (259566621818542456077/50000000000000000000)
  centralHi := (103826648727416982431/20000000000000000000)
  directionLo := (521531100478468899521/100000000000000000000)
  directionHi := (260765550239234449761/50000000000000000000)

def endpointA : IntegerEndpointWitness 110 where
  qNumerator := 22647
  qDenominator := 43472
  table := BinomialMassData.Q22647_43472.Degree110.table
  base := (53637214326475210483283785566499974547137/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 610090000000000000000000000000000000000000000
      center := (7443098)
      previous := (3721549)
      next := (3721549)
      square := (48177994221632638781882551498320000000000000)
      linear := (-5523836797608865409971107606521115000000000000)
      constant := (161605887000765668371964523986853262572146281233) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 110 interval.damping) (curvature.centralUpper 110 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22647_43472.Degree110.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 110 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree110.table
  base := (2681860657596101600586729111243766198269/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (44042)
      previous := (22021)
      next := (22021)
      square := (285076888885400229478594979280000000000000)
      linear := (-32721492258074785622135385778335000000000000)
      constant := (958316643310682628046278135947029991951502180) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 110 interval.damping) (curvature.centralUpper 110 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree110.checked
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
end ForestUnimodality.Stage99KernelData.Cell107.Kernel110

namespace ForestUnimodality.Stage99KernelData.Cell107.Kernel111
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (521531100478468899521/100000000000000000000)
  centralHi := (260765550239234449761/50000000000000000000)
  directionLo := (523917982973866515437/100000000000000000000)
  directionHi := (261958991486933257719/50000000000000000000)

def endpointA : IntegerEndpointWitness 111 where
  qNumerator := 22647
  qDenominator := 43472
  table := BinomialMassData.Q22647_43472.Degree111.table
  base := (27630545825849620348307417388731734415131/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (900614858)
      previous := (450307429)
      next := (450307429)
      square := (5829537300817549292607788731296720000000000000)
      linear := (-674458117584817683268156973618613105000000000000)
      constant := (19916080840771956653155242902043748118653719977318) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 111 interval.damping) (curvature.centralUpper 111 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22647_43472.Degree111.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 111 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree111.table
  base := (27630545295344733441800663769747829300957/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (5329082)
      previous := (2664541)
      next := (2664541)
      square := (34494303555133427766909992492880000000000000)
      linear := (-3995280267413743257662048561300295000000000000)
      constant := (118101527078219911145557060240224474863390205434) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 111 interval.damping) (curvature.centralUpper 111 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree111.checked
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
end ForestUnimodality.Stage99KernelData.Cell107.Kernel111

namespace ForestUnimodality.Stage99KernelData.Cell107.Kernel112
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (523917982973866515437/100000000000000000000)
  centralHi := (261958991486933257719/50000000000000000000)
  directionLo := (526294040437972796091/100000000000000000000)
  directionHi := (131573510109493199023/25000000000000000000)

def endpointA : IntegerEndpointWitness 112 where
  qNumerator := 22647
  qDenominator := 43472
  table := BinomialMassData.Q22647_43472.Degree112.table
  base := (56906258357872829740160179226241989954581/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (900614858)
      previous := (450307429)
      next := (450307429)
      square := (5829537300817549292607788731296720000000000000)
      linear := (-680531982658962651929809926848171295000000000000)
      constant := (20281170731117062451867397440863307740381822899709) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 112 interval.damping) (curvature.centralUpper 112 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22647_43472.Degree112.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 112 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree112.table
  base := (56906257399473599779778200814639167850917/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (5329082)
      previous := (2664541)
      next := (2664541)
      square := (34494303555133427766909992492880000000000000)
      linear := (-4031259971600437455045715443422055000000000000)
      constant := (120266434791538300083506795439159693490895905477) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 112 interval.damping) (curvature.centralUpper 112 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree112.checked
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
end ForestUnimodality.Stage99KernelData.Cell107.Kernel112

namespace ForestUnimodality.Stage99KernelData.Cell107.Kernel113
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (526294040437972796091/100000000000000000000)
  centralHi := (131573510109493199023/25000000000000000000)
  directionLo := (26432970941498819983/5000000000000000000)
  directionHi := (528659418829976399661/100000000000000000000)

def endpointA : IntegerEndpointWitness 113 where
  qNumerator := 22647
  qDenominator := 43472
  table := BinomialMassData.Q22647_43472.Degree113.table
  base := (58572714349285526542634962067241840158373/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (900614858)
      previous := (450307429)
      next := (450307429)
      square := (5829537300817549292607788731296720000000000000)
      linear := (-686605847733107620591462880077729485000000000000)
      constant := (20649581997421420201105800861281491701697883581197) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 113 interval.damping) (curvature.centralUpper 113 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22647_43472.Degree113.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 113 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree113.table
  base := (29286356741806500583128135097677611566149/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (5329082)
      previous := (2664541)
      next := (2664541)
      square := (34494303555133427766909992492880000000000000)
      linear := (-4067239675787131652429382325543815000000000000)
      constant := (122451036976412858903973815894040186501641908938) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 113 interval.damping) (curvature.centralUpper 113 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree113.checked
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
end ForestUnimodality.Stage99KernelData.Cell107.Kernel113

namespace ForestUnimodality.Stage99KernelData.Cell107.Kernel114
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (26432970941498819983/5000000000000000000)
  centralHi := (528659418829976399661/100000000000000000000)
  directionLo := (53101426085819038599/10000000000000000000)
  directionHi := (531014260858190385991/100000000000000000000)

def endpointA : IntegerEndpointWitness 114 where
  qNumerator := 22647
  qDenominator := 43472
  table := BinomialMassData.Q22647_43472.Degree114.table
  base := (15065114885080759733011761724019018343641/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 204490000000000000000000000000000000000000000
      center := (2494778)
      previous := (1247389)
      next := (1247389)
      square := (16148302772347781973982794269520000000000000)
      linear := (-1918780367887126286019711449604675000000000000)
      constant := (58230788473831073618794470651138436499436459236) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 114 interval.damping) (curvature.centralUpper 114 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22647_43472.Degree114.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 114 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree114.table
  base := (15065114689610497420704171823825281159389/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (14762)
      previous := (7381)
      next := (7381)
      square := (95552087410341905171495824080000000000000)
      linear := (-11366258670287606232169111378575000000000000)
      constant := (345305633321732149527596681685601436081144276) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 114 interval.damping) (curvature.centralUpper 114 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree114.checked
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
end ForestUnimodality.Stage99KernelData.Cell107.Kernel114

namespace ForestUnimodality.Stage99KernelData.Cell107.Kernel115
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (53101426085819038599/10000000000000000000)
  centralHi := (531014260858190385991/100000000000000000000)
  directionLo := (533358706080525254429/100000000000000000000)
  directionHi := (53335870608052525443/10000000000000000000)

def endpointA : IntegerEndpointWitness 115 where
  qNumerator := 22647
  qDenominator := 43472
  table := BinomialMassData.Q22647_43472.Degree115.table
  base := (15492373463599343898599342842451217617179/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (900614858)
      previous := (450307429)
      next := (450307429)
      square := (5829537300817549292607788731296720000000000000)
      linear := (-698753577881397557914768786536845865000000000000)
      constant := (21396368655446475209493238548069629097683533227724) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 115 interval.damping) (curvature.centralUpper 115 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22647_43472.Degree115.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 115 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree115.table
  base := (61969493148230382027514170985680927464463/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (5329082)
      previous := (2664541)
      next := (2664541)
      square := (34494303555133427766909992492880000000000000)
      linear := (-4139199084160520047196716089787335000000000000)
      constant := (126879324746427671173160282197558553592575208303) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 115 interval.damping) (curvature.centralUpper 115 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree115.checked
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
end ForestUnimodality.Stage99KernelData.Cell107.Kernel115

namespace ForestUnimodality.Stage99KernelData.Cell107.Kernel116
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (533358706080525254429/100000000000000000000)
  centralHi := (53335870608052525443/10000000000000000000)
  directionLo := (133923222750251101609/25000000000000000000)
  directionHi := (535692891001004406437/100000000000000000000)

def endpointA : IntegerEndpointWitness 116 where
  qNumerator := 22647
  qDenominator := 43472
  table := BinomialMassData.Q22647_43472.Degree116.table
  base := (63699817222991220273871578785216732922277/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (900614858)
      previous := (450307429)
      next := (450307429)
      square := (5829537300817549292607788731296720000000000000)
      linear := (-704827442955542526576421739766404055000000000000)
      constant := (21774744046095992173789536441646598397971478896653) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 116 interval.damping) (curvature.centralUpper 116 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22647_43472.Degree116.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 116 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree116.table
  base := (2547992663409462106846866226967973935657/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (5329082)
      previous := (2664541)
      next := (2664541)
      square := (34494303555133427766909992492880000000000000)
      linear := (-4175178788347214244580382971909095000000000000)
      constant := (129123010325300932540327472819072441737085835425) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 116 interval.damping) (curvature.centralUpper 116 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree116.checked
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
end ForestUnimodality.Stage99KernelData.Cell107.Kernel116

namespace ForestUnimodality.Stage99KernelData.Cell107.Kernel117
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (133923222750251101609/25000000000000000000)
  centralHi := (535692891001004406437/100000000000000000000)
  directionLo := (134504237290627727397/25000000000000000000)
  directionHi := (538016949162510909589/100000000000000000000)

def endpointA : IntegerEndpointWitness 117 where
  qNumerator := 22647
  qDenominator := 43472
  table := BinomialMassData.Q22647_43472.Degree117.table
  base := (65451429584804205829498161809004503786957/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (5329082)
      previous := (2664541)
      next := (2664541)
      square := (34494303555133427766909992492880000000000000)
      linear := (-4206516615560281036911684573940605000000000000)
      constant := (131103200062420376942641244805877262604918068717) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 117 interval.damping) (curvature.centralUpper 117 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22647_43472.Degree117.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 117 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree117.table
  base := (65451429008861560393835691161210248385941/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (5329082)
      previous := (2664541)
      next := (2664541)
      square := (34494303555133427766909992492880000000000000)
      linear := (-4211158492533908441964049854030855000000000000)
      constant := (131386390363118067729535187294873039859746288821) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 117 interval.damping) (curvature.centralUpper 117 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree117.checked
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
end ForestUnimodality.Stage99KernelData.Cell107.Kernel117

namespace ForestUnimodality.Stage99KernelData.Cell107.Kernel118
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (134504237290627727397/25000000000000000000)
  centralHi := (538016949162510909589/100000000000000000000)
  directionLo := (54033101123594387797/10000000000000000000)
  directionHi := (540331011235943877971/100000000000000000000)

def endpointA : IntegerEndpointWitness 118 where
  qNumerator := 22647
  qDenominator := 43472
  table := BinomialMassData.Q22647_43472.Degree118.table
  base := (67224330884990107898766480239728278132723/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (900614858)
      previous := (450307429)
      next := (450307429)
      square := (5829537300817549292607788731296720000000000000)
      linear := (-716975173103832463899727646225520435000000000000)
      constant := (22541458948400750088485718530295598738117514998347) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 118 interval.damping) (curvature.centralUpper 118 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22647_43472.Degree118.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 118 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree118.table
  base := (8403041295611680244311649690251140761629/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (5329082)
      previous := (2664541)
      next := (2664541)
      square := (34494303555133427766909992492880000000000000)
      linear := (-4247138196720602639347716736152615000000000000)
      constant := (133669464857511043974452733280769330636869730792) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 118 interval.damping) (curvature.centralUpper 118 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree118.checked
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
end ForestUnimodality.Stage99KernelData.Cell107.Kernel118

namespace ForestUnimodality.Stage99KernelData.Cell107.Kernel119
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (54033101123594387797/10000000000000000000)
  centralHi := (540331011235943877971/100000000000000000000)
  directionLo := (271317602552976449/50000000000000000)
  directionHi := (542635205105952898001/100000000000000000000)

def endpointA : IntegerEndpointWitness 119 where
  qNumerator := 22647
  qDenominator := 43472
  table := BinomialMassData.Q22647_43472.Degree119.table
  base := (34509260537237589336106622987591471475633/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (900614858)
      previous := (450307429)
      next := (450307429)
      square := (5829537300817549292607788731296720000000000000)
      linear := (-723049038177977432561380599455078625000000000000)
      constant := (22929798459288844555434567880950503231148168274674) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 119 interval.damping) (curvature.centralUpper 119 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22647_43472.Degree119.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 119 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree119.table
  base := (69018520604831966037871803931618857932017/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (5329082)
      previous := (2664541)
      next := (2664541)
      square := (34494303555133427766909992492880000000000000)
      linear := (-4283117900907296836731383618274375000000000000)
      constant := (135972233806361322670997698346755488333328434577) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 119 interval.damping) (curvature.centralUpper 119 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree119.checked
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
end ForestUnimodality.Stage99KernelData.Cell107.Kernel119

namespace ForestUnimodality.Stage99KernelData.Cell107.Kernel120
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (271317602552976449/50000000000000000)
  centralHi := (542635205105952898001/100000000000000000000)
  directionLo := (544929655953409669839/100000000000000000000)
  directionHi := (6811620699417620873/1250000000000000000)

def endpointA : IntegerEndpointWitness 120 where
  qNumerator := 22647
  qDenominator := 43472
  table := BinomialMassData.Q22647_43472.Degree120.table
  base := (3541700005467445403413148287743361805913/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (900614858)
      previous := (450307429)
      next := (450307429)
      square := (5829537300817549292607788731296720000000000000)
      linear := (-729122903252122401223033552684636815000000000000)
      constant := (23321459342889175810695330872690050357709009845140) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 120 interval.damping) (curvature.centralUpper 120 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22647_43472.Degree120.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 120 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree120.table
  base := (17708499921321300071734923084167879866169/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (5329082)
      previous := (2664541)
      next := (2664541)
      square := (34494303555133427766909992492880000000000000)
      linear := (-4319097605093991034115050500396135000000000000)
      constant := (138294697207773500821882575648442348641736512356) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 120 interval.damping) (curvature.centralUpper 120 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree120.checked
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
end ForestUnimodality.Stage99KernelData.Cell107.Kernel120

namespace ForestUnimodality.Stage99KernelData.Cell107.Kernel121
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (544929655953409669839/100000000000000000000)
  centralHi := (6811620699417620873/1250000000000000000)
  directionLo := (547214486334767358003/100000000000000000000)
  directionHi := (136803621583691839501/25000000000000000000)

def endpointA : IntegerEndpointWitness 121 where
  qNumerator := 22647
  qDenominator := 43472
  table := BinomialMassData.Q22647_43472.Degree121.table
  base := (36335383975159723878788226661845682332347/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 610090000000000000000000000000000000000000000
      center := (7443098)
      previous := (3721549)
      next := (3721549)
      square := (48177994221632638781882551498320000000000000)
      linear := (-6076006349803862561030466991026405000000000000)
      constant := (196003649577782544900217556375137112091828316246) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 121 interval.damping) (curvature.centralUpper 121 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22647_43472.Degree121.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 121 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree121.table
  base := (18167691891857546496391933321974138133153/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (44042)
      previous := (22021)
      next := (22021)
      square := (285076888885400229478594979280000000000000)
      linear := (-35992374456865167202468738698495000000000000)
      constant := (1162288058347535146838248997374845655464272932) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 121 interval.damping) (curvature.centralUpper 121 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree121.checked
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
end ForestUnimodality.Stage99KernelData.Cell107.Kernel121

namespace ForestUnimodality.Stage99KernelData.Cell107.Kernel122
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (547214486334767358003/100000000000000000000)
  centralHi := (136803621583691839501/25000000000000000000)
  directionLo := (27474490812922500473/5000000000000000000)
  directionHi := (549489816258450009461/100000000000000000000)

def endpointA : IntegerEndpointWitness 122 where
  qNumerator := 22647
  qDenominator := 43472
  table := BinomialMassData.Q22647_43472.Degree122.table
  base := (37264412281113388274381600481931543445597/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (900614858)
      previous := (450307429)
      next := (450307429)
      square := (5829537300817549292607788731296720000000000000)
      linear := (-741270633400412338546339459143753195000000000000)
      constant := (24114745227096826516450817465327194635620527424266) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 122 interval.damping) (curvature.centralUpper 122 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22647_43472.Degree122.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 122 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree122.table
  base := (74528824216530852255795480923913096022671/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (5329082)
      previous := (2664541)
      next := (2664541)
      square := (34494303555133427766909992492880000000000000)
      linear := (-4391057013467379428882384264639655000000000000)
      constant := (142998707361678772195614167212826437947366291951) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 122 interval.damping) (curvature.centralUpper 122 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree122.checked
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
end ForestUnimodality.Stage99KernelData.Cell107.Kernel122

namespace ForestUnimodality.Stage99KernelData.Cell107.Kernel123
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (27474490812922500473/5000000000000000000)
  centralHi := (549489816258450009461/100000000000000000000)
  directionLo := (68969470407300845679/12500000000000000000)
  directionHi := (551755763258406765433/100000000000000000000)

def endpointA : IntegerEndpointWitness 123 where
  qNumerator := 22647
  qDenominator := 43472
  table := BinomialMassData.Q22647_43472.Degree123.table
  base := (9551021239200929443553141564535938713929/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (900614858)
      previous := (450307429)
      next := (450307429)
      square := (5829537300817549292607788731296720000000000000)
      linear := (-747344498474557307207992412373311385000000000000)
      constant := (24516370227212325507469904193861645915028155341448) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 123 interval.damping) (curvature.centralUpper 123 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22647_43472.Degree123.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 123 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree123.table
  base := (76408169601507046347475747883452771728767/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (5329082)
      previous := (2664541)
      next := (2664541)
      square := (34494303555133427766909992492880000000000000)
      linear := (-4427036717654073626266051146761415000000000000)
      constant := (145380254111296946954161511948725125521884271327) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 123 interval.damping) (curvature.centralUpper 123 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree123.checked
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
end ForestUnimodality.Stage99KernelData.Cell107.Kernel123

namespace ForestUnimodality.Stage99KernelData.Cell107.Kernel124
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (68969470407300845679/12500000000000000000)
  centralHi := (551755763258406765433/100000000000000000000)
  directionLo := (554012442464958429277/100000000000000000000)
  directionHi := (277006221232479214639/50000000000000000000)

def endpointA : IntegerEndpointWitness 124 where
  qNumerator := 22647
  qDenominator := 43472
  table := BinomialMassData.Q22647_43472.Degree124.table
  base := (78308803976305328786345998711479548157501/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (900614858)
      previous := (450307429)
      next := (450307429)
      square := (5829537300817549292607788731296720000000000000)
      linear := (-753418363548702275869645365602869575000000000000)
      constant := (24921316599050334099638906805641420519928458399589) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 124 interval.damping) (curvature.centralUpper 124 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22647_43472.Degree124.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 124 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree124.table
  base := (78308803694549219203591007709719655126541/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (5329082)
      previous := (2664541)
      next := (2664541)
      square := (34494303555133427766909992492880000000000000)
      linear := (-4463016421840767823649718028883175000000000000)
      constant := (147781495307691528130710580316893084255582437421) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 124 interval.damping) (curvature.centralUpper 124 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree124.checked
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
end ForestUnimodality.Stage99KernelData.Cell107.Kernel124

namespace ForestUnimodality.Stage99KernelData.Cell107.Kernel125
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (554012442464958429277/100000000000000000000)
  centralHi := (277006221232479214639/50000000000000000000)
  directionLo := (278129983336528612501/50000000000000000000)
  directionHi := (556259966673057225003/100000000000000000000)

def endpointA : IntegerEndpointWitness 125 where
  qNumerator := 22647
  qDenominator := 43472
  table := BinomialMassData.Q22647_43472.Degree125.table
  base := (80230726725123678961492208287197736009227/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (900614858)
      previous := (450307429)
      next := (450307429)
      square := (5829537300817549292607788731296720000000000000)
      linear := (-759492228622847244531298318832427765000000000000)
      constant := (25329584342424847440408415537979029607193618535203) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 125 interval.damping) (curvature.centralUpper 125 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22647_43472.Degree125.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 125 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree125.table
  base := (20057681617693473809885548530438597303683/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (5329082)
      previous := (2664541)
      next := (2664541)
      square := (34494303555133427766909992492880000000000000)
      linear := (-4498996126027462021033384911004935000000000000)
      constant := (150202430949775580628250500503111728475288708492) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 125 interval.damping) (curvature.centralUpper 125 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree125.checked
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
end ForestUnimodality.Stage99KernelData.Cell107.Kernel125

namespace ForestUnimodality.Stage99KernelData.Cell107.Kernel126
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (278129983336528612501/50000000000000000000)
  centralHi := (556259966673057225003/100000000000000000000)
  directionLo := (69812305801009282401/12500000000000000000)
  directionHi := (558498446408074259209/100000000000000000000)

def endpointA : IntegerEndpointWitness 126 where
  qNumerator := 22647
  qDenominator := 43472
  table := BinomialMassData.Q22647_43472.Degree126.table
  base := (41086969068756878423457720674378580345271/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (900614858)
      previous := (450307429)
      next := (450307429)
      square := (5829537300817549292607788731296720000000000000)
      linear := (-765566093696992213192951272061985955000000000000)
      constant := (25741173457169408803788196695011438525229882502238) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 126 interval.damping) (curvature.centralUpper 126 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22647_43472.Degree126.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 126 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree126.table
  base := (41086968953957790181251622425891247169967/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (5329082)
      previous := (2664541)
      next := (2664541)
      square := (34494303555133427766909992492880000000000000)
      linear := (-4534975830214156218417051793126695000000000000)
      constant := (152643061036576525399312537281462401135262657054) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 126 interval.damping) (curvature.centralUpper 126 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree126.checked
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
end ForestUnimodality.Stage99KernelData.Cell107.Kernel126

namespace ForestUnimodality.Stage99KernelData.Cell107.Kernel127
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (69812305801009282401/12500000000000000000)
  centralHi := (558498446408074259209/100000000000000000000)
  directionLo := (112145597997844651231/20000000000000000000)
  directionHi := (140181997497305814039/25000000000000000000)

def endpointA : IntegerEndpointWitness 127 where
  qNumerator := 22647
  qDenominator := 43472
  table := BinomialMassData.Q22647_43472.Degree127.table
  base := (10517304774162059246518003020737145073641/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (900614858)
      previous := (450307429)
      next := (450307429)
      square := (5829537300817549292607788731296720000000000000)
      linear := (-771639958771137181854604225291544145000000000000)
      constant := (26156083943135054362750354509282901076816235328392) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 127 interval.damping) (curvature.centralUpper 127 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22647_43472.Degree127.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 127 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree127.table
  base := (84138437986051229915790211368400692429603/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (5329082)
      previous := (2664541)
      next := (2664541)
      square := (34494303555133427766909992492880000000000000)
      linear := (-4570955534400850415800718675248455000000000000)
      constant := (155103385567224103930248079096144875646017488643) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 127 interval.damping) (curvature.centralUpper 127 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree127.checked
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
end ForestUnimodality.Stage99KernelData.Cell107.Kernel127

namespace ForestUnimodality.Stage99KernelData.Cell107.Kernel128
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (112145597997844651231/20000000000000000000)
  centralHi := (140181997497305814039/25000000000000000000)
  directionLo := (281474351795361772769/50000000000000000000)
  directionHi := (562948703590723545539/100000000000000000000)

def endpointA : IntegerEndpointWitness 128 where
  qNumerator := 22647
  qDenominator := 43472
  table := BinomialMassData.Q22647_43472.Degree128.table
  base := (21531056718603336981024086490128867477463/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (900614858)
      previous := (450307429)
      next := (450307429)
      square := (5829537300817549292607788731296720000000000000)
      linear := (-777713823845282150516257178521102335000000000000)
      constant := (26574315800188474792916585765766107084751349440828) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 128 interval.damping) (curvature.centralUpper 128 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22647_43472.Degree128.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 128 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree128.table
  base := (43062113343676907434624607675398004957991/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (5329082)
      previous := (2664541)
      next := (2664541)
      square := (34494303555133427766909992492880000000000000)
      linear := (-4606935238587544613184385557370215000000000000)
      constant := (157583404540939613765990974388227720509140009742) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 128 interval.damping) (curvature.centralUpper 128 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree128.checked
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
end ForestUnimodality.Stage99KernelData.Cell107.Kernel128

namespace ForestUnimodality.Stage99KernelData.Cell107.Kernel129
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (281474351795361772769/50000000000000000000)
  centralHi := (562948703590723545539/100000000000000000000)
  directionLo := (56516069130080002203/10000000000000000000)
  directionHi := (565160691300800022031/100000000000000000000)

def endpointA : IntegerEndpointWitness 129 where
  qNumerator := 22647
  qDenominator := 43472
  table := BinomialMassData.Q22647_43472.Degree129.table
  base := (44065652082351861839284640031029516936353/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (900614858)
      previous := (450307429)
      next := (450307429)
      square := (5829537300817549292607788731296720000000000000)
      linear := (-783787688919427119177910131750660525000000000000)
      constant := (26995869028210370700599925829300760219427330362834) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 129 interval.damping) (curvature.centralUpper 129 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22647_43472.Degree129.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 129 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree129.table
  base := (88131303995871895862787009092899836979909/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (5329082)
      previous := (2664541)
      next := (2664541)
      square := (34494303555133427766909992492880000000000000)
      linear := (-4642914942774238810568052439491975000000000000)
      constant := (160083117957026280083852990004662152779119405029) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 129 interval.damping) (curvature.centralUpper 129 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree129.checked
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
end ForestUnimodality.Stage99KernelData.Cell107.Kernel129
