import Ragu.Meta.TrustBoundary

/-!
# Trust-boundary census completeness

`Ragu.Meta.TrustBoundary` imports every current formal-circuit theorem module and records each direct
trust assertion. This command checks the elaborated environment, complementing the source-tree
coverage check in `scripts/check_fv_endpoint_census.sh`.
-/

assert_endpoint_census
