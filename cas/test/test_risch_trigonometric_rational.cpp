#include"../prec_cas.hpp"

#include<algorithm>
#include<cassert>
#include<cstdio>

int main(){
    exact_context context;
    exact_expr x = context.symbol("x");

    for(int degree : {4, 6, 8}){
        exact_expr denominator = context.power(x, context.integer(degree)) +
            context.integer(1);
        if(degree == 4)
            denominator = context.power(x, context.integer(4)) +
                context.power(x, context.integer(2)) + context.integer(1);
        exact_expr integrand = context.integer(1) / denominator;
        risch_result rational_result = context.integrate_elementary(
            integrand, x);
        assert(rational_result.status == risch_status::elementary);
        exact_expr expanded_primitive = context.expand(
            rational_result.elementary_part);
        exact_expr derivative_error = context.simplify(
            context.differentiate(expanded_primitive, x) - integrand);
        if(derivative_error != context.integer(0))
            std::fprintf(stderr, "degree %d derivative error: %s\n", degree,
                         derivative_error.to_string().c_str());
        assert(derivative_error == context.integer(0));
    }

    exact_expr irreducible_quartic = context.power(x, context.integer(4)) +
        context.power(x, context.integer(2)) + x + context.integer(1);
    exact_expr quartic_integrand = context.integer(1) / irreducible_quartic;
    risch_result quartic_result = context.integrate_elementary(
        quartic_integrand, x);
    assert(quartic_result.status == risch_status::elementary);
    exact_expr expanded_quartic = context.expand(
        quartic_result.elementary_part);
    assert(expanded_quartic.valid());
    assert(expanded_quartic.operation() != exact_opcode::integral);
    assert(context.simplify(context.differentiate(
        quartic_result.elementary_part, x) -
        quartic_integrand) == context.integer(0));

    exact_expr sine_x = context.sine(x);
    risch_result sine_result = context.integrate_elementary(sine_x, x);
    assert(sine_result.status == risch_status::elementary);
    assert(sine_result.remainder == context.integer(0));
    assert(sine_result.elementary_part.valid());

    exact_expr exp_x2 = context.exponential(context.power(x,
        context.integer(2)));
    exact_expr polynomial_exp_input =
        (context.integer(1) + context.integer(2) * context.power(x,
            context.integer(2))) * exp_x2;
    risch_result polynomial_exp_result = context.integrate_elementary(
        polynomial_exp_input, x);
    assert(polynomial_exp_result.status == risch_status::elementary);
    assert(polynomial_exp_result.remainder == context.integer(0));
    assert(context.simplify(context.differentiate(
        polynomial_exp_result.elementary_part, x) - polynomial_exp_input) ==
        context.integer(0));

    exact_expr polynomial_hyperbolic_input =
        (context.integer(8) * context.power(x, context.integer(2)) +
         context.integer(2)) * exp_x2 * context.hyperbolic_sine(x);
    risch_result polynomial_hyperbolic_result = context.integrate_elementary(
        polynomial_hyperbolic_input, x);
    if(polynomial_hyperbolic_result.status != risch_status::elementary ||
       polynomial_hyperbolic_result.remainder != context.integer(0)){
        std::fprintf(stderr, "polynomial-rate hyperbolic RDE failed: %s\n",
            polynomial_hyperbolic_result.diagnostic.c_str());
        return 1;
    }
    exact_expr expected_positive_mode = context.exponential(
        context.power(x, context.integer(2)) + x);
    exact_expr expected_negative_mode = context.exponential(
        context.power(x, context.integer(2)) - x);
    exact_expr expected_mode_primitive =
        (context.integer(2) * x - context.integer(1)) *
            expected_positive_mode -
        (context.integer(2) * x + context.integer(1)) *
            expected_negative_mode;
    exact_expr expected_mode_input =
        (context.integer(4) * context.power(x, context.integer(2)) +
         context.integer(1)) *
        (expected_positive_mode - expected_negative_mode);
    if(context.simplify(polynomial_hyperbolic_result.elementary_part -
            expected_mode_primitive) != context.integer(0) ||
       context.simplify(context.differentiate(
            polynomial_hyperbolic_result.elementary_part, x) -
            expected_mode_input) != context.integer(0)){
        std::fprintf(stderr, "polynomial-rate hyperbolic mode identity failed\n  got=%s\n  derivative error=%s\n",
            polynomial_hyperbolic_result.elementary_part.to_string().c_str(),
            context.simplify(context.differentiate(
                polynomial_hyperbolic_result.elementary_part, x) -
                expected_mode_input).to_string().c_str());
        return 1;
    }
    exact_expr no_polynomial_mode_solution = exp_x2 *
        context.hyperbolic_sine(x);
    assert(context.integrate_elementary(no_polynomial_mode_solution, x).status !=
        risch_status::elementary);

    exact_expr rational_trig = sine_x /
        (context.integer(2) + context.cosine(x));
    risch_result rational_trig_result = context.integrate_elementary(
        rational_trig, x);
    assert(rational_trig_result.status == risch_status::elementary);
    assert(rational_trig_result.remainder == context.integer(0));

    for(const exact_expr &mixed_frequency : {
            context.integer(1) / (context.integer(3) + context.cosine(x) +
                context.sine(context.integer(2) * x)),
            context.integer(1) / (context.integer(3) +
                context.sine(context.integer(2) * x) + context.cosine(x)),
            context.integer(1) / (context.integer(5) +
                context.sine(context.integer(3) * x) +
                context.cosine(context.integer(2) * x))}){
        risch_result mixed_result = context.integrate_elementary(
            mixed_frequency, x);
        if(mixed_result.status != risch_status::elementary ||
           mixed_result.remainder != context.integer(0)){
            std::fprintf(stderr, "mixed-frequency trig RDE failed: %s\n",
                mixed_result.diagnostic.c_str());
            std::fprintf(stderr, "  input=%s status=%d primitive=%s remainder=%s\n",
                mixed_frequency.to_string().c_str(), (int)mixed_result.status,
                mixed_result.elementary_part.to_string().c_str(),
                mixed_result.remainder.to_string().c_str());
            return 1;
        }
    }

    // Rationally commensurate slopes share a smaller exact base angle:
    // x/2, x/3, and x/4 become frequencies 6, 4, and 3 of x/12.
    exact_expr x_over_two = x / context.integer(2);
    exact_expr x_over_three = x / context.integer(3);
    exact_expr x_over_four = x / context.integer(4);
    exact_expr rationally_commensurate = context.integer(1) /
        (context.integer(5) + context.cosine(x_over_two) +
         context.sine(x_over_three) + context.cosine(x_over_four));
    risch_result rational_lattice_result = context.integrate_elementary(
        rationally_commensurate, x);
    if(rational_lattice_result.status != risch_status::elementary ||
       rational_lattice_result.remainder != context.integer(0)){
        std::fprintf(stderr, "rational-frequency trig RDE failed: %s\n",
            rational_lattice_result.diagnostic.c_str());
        return 1;
    }
    exact_expr reversed_rationally_commensurate = context.integer(1) /
        (context.integer(5) + context.cosine(x_over_four) +
         context.sine(x_over_three) + context.cosine(x_over_two));
    risch_result reversed_rational_lattice_result = context.integrate_elementary(
        reversed_rationally_commensurate, x);
    assert(reversed_rational_lattice_result.status ==
        risch_status::elementary);
    assert(reversed_rational_lattice_result.remainder == context.integer(0));

    exact_expr negative_frequency_rational = context.integer(1) /
        (context.integer(5) + context.cosine(-x_over_two) +
         context.sine(x_over_three) +
         context.cosine(-x_over_four + context.integer(6) * context.pi()));
    risch_result negative_frequency_result = context.integrate_elementary(
        negative_frequency_rational, x);
    if(negative_frequency_result.status != risch_status::elementary ||
       negative_frequency_result.remainder != context.integer(0)){
        std::fprintf(stderr, "negative rational-frequency trig RDE failed: %s\n",
            negative_frequency_result.diagnostic.c_str());
        return 1;
    }

    exact_expr phase_shifted_rationally_commensurate = context.integer(1) /
        (context.integer(5) +
         context.cosine(x_over_two) +
         context.sine(x_over_three + context.integer(6) * context.pi()) +
         context.cosine(x_over_four));
    risch_result phase_shifted_lattice_result = context.integrate_elementary(
        phase_shifted_rationally_commensurate, x);
    if(phase_shifted_lattice_result.status != risch_status::elementary ||
       phase_shifted_lattice_result.remainder != context.integer(0)){
        std::fprintf(stderr, "phase-shifted rational-frequency RDE failed: %s\n",
            phase_shifted_lattice_result.diagnostic.c_str());
        return 1;
    }
    exact_expr unsupported_phase = context.integer(1) /
        (context.integer(3) +
         context.cosine(x_over_two + context.rational(
             precq_t(precn_t(1), precn_t(2)))) +
         context.sine(x_over_three));
    assert(context.integrate_elementary(unsupported_phase, x).status ==
        risch_status::unsupported);

    exact_expr irrational_frequency = context.integer(1) /
        (context.integer(3) + context.cosine(x) +
         context.sine(context.square_root(context.integer(2)) * x));
    risch_result irrational_frequency_result = context.integrate_elementary(
        irrational_frequency, x);
    assert(irrational_frequency_result.status == risch_status::unsupported);

    exact_expr symbolic_frequency = context.symbol("trig_frequency");
    exact_expr symbolic_mixed_frequency = context.integer(1) /
        (context.integer(3) + context.cosine(symbolic_frequency * x) +
         context.sine(context.integer(2) * symbolic_frequency * x));
    risch_result symbolic_mixed_result = context.integrate_elementary(
        symbolic_mixed_frequency, x);
    assert(symbolic_mixed_result.status == risch_status::elementary);
    assert(symbolic_mixed_result.remainder == context.integer(0));
    assert(std::find(symbolic_mixed_result.conditions.begin(),
        symbolic_mixed_result.conditions.end(), symbolic_frequency) !=
        symbolic_mixed_result.conditions.end());

    exact_expr tangent_result_input = context.tangent(x);
    risch_result tangent_result = context.integrate_elementary(
        tangent_result_input, x);
    assert(tangent_result.status == risch_status::elementary);
    assert(tangent_result.remainder == context.integer(0));

    exact_expr hyperbolic_rational = context.hyperbolic_sine(x) /
        (context.integer(2) + context.hyperbolic_cosine(x));
    risch_result hyperbolic_result = context.integrate_elementary(
        hyperbolic_rational, x);
    assert(hyperbolic_result.status == risch_status::elementary);
    assert(hyperbolic_result.remainder == context.integer(0));

    exact_expr hyperbolic_tangent = context.hyperbolic_tangent(x);
    risch_result hyperbolic_tangent_result = context.integrate_elementary(
        hyperbolic_tangent, x);
    assert(hyperbolic_tangent_result.status == risch_status::elementary);
    assert(hyperbolic_tangent_result.remainder == context.integer(0));

    exact_expr affine_angle = context.integer(2) * x + context.integer(1);
    exact_expr affine_integrand = context.integer(2) *
        context.cosine(affine_angle);
    risch_result affine_result = context.integrate_elementary(
        affine_integrand, x);
    if(affine_result.status != risch_status::elementary)
        std::fprintf(stderr, "affine status=%d diagnostic=%s remainder=%s\n",
            (int)affine_result.status, affine_result.diagnostic.c_str(),
            affine_result.remainder.valid()
                ? affine_result.remainder.to_string().c_str() : "<invalid>");
    assert(affine_result.status == risch_status::elementary);
    assert(affine_result.remainder == context.integer(0));

    exact_expr rational_slope_angle = x / context.integer(2) +
        context.rational(precq_t(precn_t(1), precn_t(3)));
    exact_expr rational_slope_integrand =
        context.cosine(rational_slope_angle) / context.integer(2);
    risch_result rational_slope_result = context.integrate_elementary(
        rational_slope_integrand, x);
    assert(rational_slope_result.status == risch_status::elementary);
    assert(rational_slope_result.remainder == context.integer(0));

    exact_expr symbolic_slope = context.symbol("trig_rate");
    exact_expr symbolic_slope_input = context.integer(1) /
        (context.integer(2) + context.cosine(symbolic_slope*x));
    risch_result symbolic_slope_result = context.integrate_elementary(
        symbolic_slope_input,x);
    assert(symbolic_slope_result.status == risch_status::elementary);
    assert(symbolic_slope_result.remainder == context.integer(0));
    assert(std::find(symbolic_slope_result.conditions.begin(),
        symbolic_slope_result.conditions.end(),symbolic_slope) !=
        symbolic_slope_result.conditions.end());
    assert(symbolic_slope_result.conditions.size() == 1);
    context.assume(symbolic_slope,"positive");
    risch_result positive_slope_result = context.integrate_elementary(
        symbolic_slope_input,x);
    assert(positive_slope_result.status == risch_status::elementary);
    assert(positive_slope_result.conditions.empty());

    exact_expr hyperbolic_slope = context.symbol("hyperbolic_rate");
    exact_expr hyperbolic_parameter = context.symbol("hyperbolic_parameter");
    exact_expr rationalized_hyperbolic = context.integer(2) /
        (context.integer(3)-context.power(hyperbolic_parameter,
                                           context.integer(2)));
    assert(context.integrate_elementary(rationalized_hyperbolic,
        hyperbolic_parameter).status == risch_status::elementary);
    exact_expr hyperbolic_baseline = context.integer(1) /
        (context.integer(2) + context.hyperbolic_cosine(x));
    risch_result hyperbolic_baseline_result = context.integrate_elementary(
        hyperbolic_baseline,x);
    assert(hyperbolic_baseline_result.status == risch_status::elementary);
    exact_expr symbolic_hyperbolic_input = context.integer(1) /
        (context.integer(2) +
         context.hyperbolic_cosine(hyperbolic_slope*x));
    risch_result symbolic_hyperbolic_result = context.integrate_elementary(
        symbolic_hyperbolic_input,x);
    if(symbolic_hyperbolic_result.status != risch_status::elementary)
        std::fprintf(stderr,"symbolic hyperbolic status=%d: %s; remainder=%s\n",
            (int)symbolic_hyperbolic_result.status,
            symbolic_hyperbolic_result.diagnostic.c_str(),
            symbolic_hyperbolic_result.remainder.to_string().c_str());
    assert(symbolic_hyperbolic_result.status == risch_status::elementary);
    assert(symbolic_hyperbolic_result.remainder == context.integer(0));
    assert(std::find(symbolic_hyperbolic_result.conditions.begin(),
        symbolic_hyperbolic_result.conditions.end(),hyperbolic_slope) !=
        symbolic_hyperbolic_result.conditions.end());

    exact_expr phase = context.symbol("phase");
    for(const exact_expr &offset : {phase, context.pi() / context.integer(3)}){
        exact_expr shifted_angle = x + offset;
        exact_expr shifted_rational_trig = context.integer(1) /
            (context.integer(2) + context.cosine(shifted_angle));
        risch_result shifted_rational_trig_result =
            context.integrate_elementary(shifted_rational_trig, x);
        assert(shifted_rational_trig_result.status == risch_status::elementary);
        assert(shifted_rational_trig_result.remainder == context.integer(0));
    }

    exact_expr exponential_factor = context.exponential(context.integer(2) * x);
    exact_expr affine_trig_angle = context.integer(3) * x + context.integer(1);
    exact_expr exponential_sine = exponential_factor *
        context.sine(affine_trig_angle);
    risch_result exponential_sine_result = context.integrate_elementary(
        exponential_sine, x);
    assert(exponential_sine_result.status == risch_status::elementary);
    assert(exponential_sine_result.remainder == context.integer(0));
    exact_expr exponential_sine_error = context.simplify(context.differentiate(
        exponential_sine_result.elementary_part, x) - exponential_sine);
    if(exponential_sine_error != context.integer(0))
        std::fprintf(stderr, "exp-sine derivative mismatch: %s\nprimitive: %s\n",
            exponential_sine_error.to_string().c_str(),
            exponential_sine_result.elementary_part.to_string().c_str());
    assert(exponential_sine_error == context.integer(0));

    exact_expr quadratic_exponential_hyperbolic = context.power(
        x, context.integer(2)) * context.exponential(x) *
        context.hyperbolic_sine(x);
    risch_result quadratic_exponential_hyperbolic_result =
        context.integrate_elementary(quadratic_exponential_hyperbolic, x);
    assert(quadratic_exponential_hyperbolic_result.status ==
        risch_status::elementary);
    assert(quadratic_exponential_hyperbolic_result.remainder ==
        context.integer(0));
    exact_expr quadratic_exponential_hyperbolic_euler =
        context.power(x, context.integer(2)) *
        (context.exponential(context.integer(2) * x) - context.integer(1)) /
        context.integer(2);
    assert(context.simplify(context.expand(context.differentiate(
        quadratic_exponential_hyperbolic_result.elementary_part, x) -
        quadratic_exponential_hyperbolic_euler)) == context.integer(0));

    exact_expr exponential_cosine = context.exponential(x) *
        context.cosine(context.integer(2) * x);
    risch_result exponential_cosine_result = context.integrate_elementary(
        exponential_cosine, x);
    assert(exponential_cosine_result.status == risch_status::elementary);
    assert(exponential_cosine_result.remainder == context.integer(0));
    assert(context.simplify(context.differentiate(
        exponential_cosine_result.elementary_part, x) -
        exponential_cosine) == context.integer(0));

    exact_expr a = context.symbol("a");
    exact_expr b = context.symbol("b");
    exact_expr symbolic_exponential_sine = context.exponential(a * x) *
        context.sine(b * x);
    risch_result symbolic_exponential_sine_result =
        context.integrate_elementary(symbolic_exponential_sine, x);
    assert(symbolic_exponential_sine_result.status == risch_status::elementary);
    assert(!symbolic_exponential_sine_result.conditions.empty());
    exact_expr symbolic_trig_denominator = context.power(a, context.integer(2)) +
        context.power(b, context.integer(2));
    bool has_symbolic_trig_denominator = false;
    for(const exact_expr &condition : symbolic_exponential_sine_result.conditions)
        if(context.simplify(condition - symbolic_trig_denominator) ==
           context.integer(0)){
            has_symbolic_trig_denominator = true;
            break;
        }
    assert(has_symbolic_trig_denominator);
    context.assume(a, "positive");
    context.assume(b, "real");
    risch_result positive_exponential_sine_result =
        context.integrate_elementary(symbolic_exponential_sine, x);
    assert(positive_exponential_sine_result.status == risch_status::elementary);
    assert(positive_exponential_sine_result.conditions.empty());

    exact_expr exponential_hyperbolic_sine =
        context.exponential(context.integer(2) * x) *
        context.hyperbolic_sine(context.integer(3) * x + context.integer(1));
    risch_result exponential_hyperbolic_sine_result =
        context.integrate_elementary(exponential_hyperbolic_sine, x);
    assert(exponential_hyperbolic_sine_result.status ==
        risch_status::elementary);
    exact_expr hyperbolic_plus = context.exponential(
        context.integer(5) * x + context.integer(1));
    exact_expr hyperbolic_minus = context.exponential(-x - context.integer(1));
    assert(context.simplify(context.differentiate(
        exponential_hyperbolic_sine_result.elementary_part, x) -
        (hyperbolic_plus - hyperbolic_minus) / context.integer(2)) ==
        context.integer(0));

    exact_expr exponential_hyperbolic_cosine =
        context.exponential(context.integer(2) * x) *
        context.hyperbolic_cosine(context.integer(3) * x + context.integer(1));
    risch_result exponential_hyperbolic_cosine_result =
        context.integrate_elementary(exponential_hyperbolic_cosine, x);
    assert(exponential_hyperbolic_cosine_result.status ==
        risch_status::elementary);
    assert(context.simplify(context.differentiate(
        exponential_hyperbolic_cosine_result.elementary_part, x) -
        (hyperbolic_plus + hyperbolic_minus) / context.integer(2)) ==
        context.integer(0));

    exact_expr circular_angle = context.i() * x;
    exact_expr exponential_circular_hyperbolic = context.exponential(x) *
        context.sine(x) * context.hyperbolic_sine(context.integer(2) * x);
    risch_result exponential_circular_hyperbolic_result =
        context.integrate_elementary(exponential_circular_hyperbolic, x);
    assert(exponential_circular_hyperbolic_result.status ==
        risch_status::elementary);
    exact_expr quarter_i = context.i() / context.integer(4);
    exact_expr expanded_circular_hyperbolic =
        -quarter_i * context.exponential(context.integer(3) * x + circular_angle) +
         quarter_i * context.exponential(-x + circular_angle) +
         quarter_i * context.exponential(context.integer(3) * x - circular_angle) -
         quarter_i * context.exponential(-x - circular_angle);
    assert(context.simplify(context.differentiate(
        exponential_circular_hyperbolic_result.elementary_part, x) -
        expanded_circular_hyperbolic) ==
        context.integer(0));

    exact_expr exponential_sine_square = context.exponential(x) *
        context.power(context.sine(x), context.integer(2));
    risch_result exponential_sine_square_result = context.integrate_elementary(
        exponential_sine_square, x);
    assert(exponential_sine_square_result.status == risch_status::elementary);
    exact_expr expanded_exponential_sine_square =
        -context.exponential(x + context.integer(2) * circular_angle) /
            context.integer(4) +
         context.exponential(x) / context.integer(2) -
         context.exponential(x - context.integer(2) * circular_angle) /
            context.integer(4);
    assert(context.simplify(context.differentiate(
        exponential_sine_square_result.elementary_part, x) -
        expanded_exponential_sine_square) == context.integer(0));

    exact_expr resonant_hyperbolic = context.exponential(x) *
        context.hyperbolic_sine(x);
    risch_result resonant_hyperbolic_result = context.integrate_elementary(
        resonant_hyperbolic, x);
    assert(resonant_hyperbolic_result.status == risch_status::elementary);
    assert(context.simplify(context.differentiate(
        resonant_hyperbolic_result.elementary_part, x) -
        (context.exponential(context.integer(2) * x) - context.integer(1)) /
            context.integer(2)) == context.integer(0));

    exact_expr resonant_hyperbolic_cosine = context.exponential(x) *
        context.hyperbolic_cosine(x);
    risch_result resonant_hyperbolic_cosine_result =
        context.integrate_elementary(resonant_hyperbolic_cosine, x);
    assert(resonant_hyperbolic_cosine_result.status ==
        risch_status::elementary);
    assert(context.simplify(context.differentiate(
        resonant_hyperbolic_cosine_result.elementary_part, x) -
        (context.exponential(context.integer(2) * x) + context.integer(1)) /
            context.integer(2)) == context.integer(0));

    exact_expr symbolic_exponential_cosh = context.exponential(a * x) *
        context.hyperbolic_cosine(b * x);
    risch_result symbolic_exponential_cosh_result =
        context.integrate_elementary(symbolic_exponential_cosh, x);
    assert(symbolic_exponential_cosh_result.status == risch_status::elementary);
    assert(symbolic_exponential_cosh_result.conditions.size() == 2);

    exact_expr symbolic_exponential_sinh = context.exponential(a * x) *
        context.hyperbolic_sine(b * x);
    risch_result symbolic_exponential_sinh_result =
        context.integrate_elementary(symbolic_exponential_sinh, x);
    assert(symbolic_exponential_sinh_result.status == risch_status::elementary);
    assert(symbolic_exponential_sinh_result.conditions.size() == 2);

    exact_expr c = context.symbol("c");
    exact_expr symbolic_multiangle_hyperbolic = context.exponential(a * x) *
        context.hyperbolic_sine(b * x) * context.hyperbolic_cosine(c * x);
    risch_result symbolic_multiangle_result = context.integrate_elementary(
        symbolic_multiangle_hyperbolic, x);
    assert(symbolic_multiangle_result.status == risch_status::elementary);
    assert(symbolic_multiangle_result.conditions.size() == 4);
    exact_expr expanded_symbolic_multiangle =
        (context.exponential((a + b + c) * x) +
         context.exponential((a + b - c) * x) -
         context.exponential((a - b + c) * x) -
         context.exponential((a - b - c) * x)) / context.integer(4);
    assert(context.simplify(context.differentiate(
        symbolic_multiangle_result.elementary_part, x) -
        expanded_symbolic_multiangle) == context.integer(0));

    exact_expr affine_hyperbolic_angle = context.integer(2) * x +
        context.integer(1);
    exact_expr affine_hyperbolic_integrand = context.integer(2) *
        context.hyperbolic_cosine(affine_hyperbolic_angle);
    risch_result affine_hyperbolic_result = context.integrate_elementary(
        affine_hyperbolic_integrand, x);
    assert(affine_hyperbolic_result.status == risch_status::elementary);
    assert(affine_hyperbolic_result.remainder == context.integer(0));

    exact_expr exponential_sinh_square = context.exponential(x) *
        context.power(context.hyperbolic_sine(x), context.integer(2));
    risch_result exponential_sinh_square_result = context.integrate_elementary(
        exponential_sinh_square, x);
    assert(exponential_sinh_square_result.status == risch_status::elementary);
    exact_expr expanded_sinh_square =
        (context.exponential(context.integer(3) * x) -
         context.integer(2) * context.exponential(x) +
         context.exponential(-x)) / context.integer(4);
    assert(context.simplify(context.differentiate(
        exponential_sinh_square_result.elementary_part, x) -
        expanded_sinh_square) == context.integer(0));

    exact_expr exponential_sinh_cosh = context.exponential(x) *
        context.hyperbolic_sine(x) * context.hyperbolic_cosine(x);
    risch_result exponential_sinh_cosh_result = context.integrate_elementary(
        exponential_sinh_cosh, x);
    assert(exponential_sinh_cosh_result.status == risch_status::elementary);
    exact_expr expanded_sinh_cosh =
        (context.exponential(context.integer(3) * x) -
         context.exponential(-x)) / context.integer(4);
    assert(context.simplify(context.differentiate(
        exponential_sinh_cosh_result.elementary_part, x) -
        expanded_sinh_cosh) == context.integer(0));

    exact_expr mixed_hyperbolic_angles = context.exponential(x) *
        context.hyperbolic_sine(x) *
        context.hyperbolic_cosine(context.integer(2) * x);
    risch_result mixed_hyperbolic_angles_result = context.integrate_elementary(
        mixed_hyperbolic_angles, x);
    assert(mixed_hyperbolic_angles_result.status == risch_status::elementary);
    exact_expr expanded_mixed_hyperbolic =
        (context.exponential(context.integer(4) * x) + context.integer(1) -
         context.exponential(context.integer(2) * x) -
         context.exponential(-context.integer(2) * x)) / context.integer(4);
    assert(context.simplify(context.differentiate(
        mixed_hyperbolic_angles_result.elementary_part, x) -
        expanded_mixed_hyperbolic) == context.integer(0));

    exact_expr resonant_cosh_square = context.exponential(-context.integer(4) * x) *
        context.power(context.hyperbolic_cosine(context.integer(2) * x),
                      context.integer(2));
    risch_result resonant_cosh_square_result = context.integrate_elementary(
        resonant_cosh_square, x);
    assert(resonant_cosh_square_result.status == risch_status::elementary);
    exact_expr expanded_cosh_square = (context.integer(1) +
        context.integer(2) * context.exponential(-context.integer(4) * x) +
        context.exponential(-context.integer(8) * x)) / context.integer(4);
    assert(context.simplify(context.differentiate(
        resonant_cosh_square_result.elementary_part, x) -
        expanded_cosh_square) == context.integer(0));

    std::puts("risch trigonometric rational ok");
    return 0;
}
