#!/bin/bash

# Script to test all examples with different solver configurations
# Tests each .scm file with various combinations of solvers disabled
#
# Usage:
#   ./test-solvers.sh                          # Test all configs, all files
#   ./test-solvers.sh --configs "no-vampire"   # Test specific configs
#   ./test-solvers.sh --files "basic-hash.scm" # Test specific files
#   ./test-solvers.sh --dry-run                # Show what would be tested
#
# Environment variables:
#   SOLVER_CONFIGS - Space-separated list of configs to test
#   TEST_FILES - Space-separated list of files to test
#   TEST_TIMEOUT - Timeout per test in seconds (default: 300)

set -e

# Configuration
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
BINARY_NAME="indistinguishability"
RESULTS_DIR="$SCRIPT_DIR/solver-test-results"

# All available solver configurations
declare -A SOLVER_ENV_MAP=(
    ["all-enabled"]=""
    ["no-vampire"]="DISABLE_VAMPIRE=1"
    ["no-z3"]="DISABLE_Z3=1"
    ["no-cvc5"]="DISABLE_CVC5=1"
    ["vampire-only"]="DISABLE_Z3=1,DISABLE_CVC5=1"
    ["z3-only"]="DISABLE_VAMPIRE=1,DISABLE_CVC5=1"
    ["cvc5-only"]="DISABLE_VAMPIRE=1,DISABLE_Z3=1"
    ["no-solvers"]="DISABLE_VAMPIRE=1,DISABLE_Z3=1,DISABLE_CVC5=1"
)

# Default timeout per test (1 hour)
TEST_TIMEOUT="${TEST_TIMEOUT:-3600}"

# Parse command line arguments
CONFIGS_TO_TEST=()
FILES_TO_TEST=()
DRY_RUN=false

while [[ $# -gt 0 ]]; do
    case $1 in
        --configs)
            IFS=' ' read -ra CONFIGS_TO_TEST <<< "$2"
            shift 2
            ;;
        --files)
            IFS=' ' read -ra FILES_TO_TEST <<< "$2"
            shift 2
            ;;
        --dry-run)
            DRY_RUN=true
            shift
            ;;
        --timeout)
            TEST_TIMEOUT="$2"
            shift 2
            ;;
        -h|--help)
            echo "Usage: $0 [OPTIONS]"
            echo ""
            echo "Options:"
            echo "  --configs CONFIGS   Space-separated list of configs to test"
            echo "                      Available: ${!SOLVER_ENV_MAP[*]}"
            echo "  --files FILES       Space-separated list of .scm files to test"
            echo "  --timeout SECONDS   Timeout per test in seconds (default: 300)"
            echo "  --dry-run           Show test plan without running"
            echo "  -h, --help          Show this help"
            echo ""
            echo "Environment variables:"
            echo "  SOLVER_CONFIGS      Same as --configs"
            echo "  TEST_FILES          Same as --files"
            echo "  TEST_TIMEOUT        Same as --timeout"
            exit 0
            ;;
        *)
            echo "Unknown option: $1"
            exit 1
            ;;
    esac
done

# Use environment variables if not specified via CLI
if [ ${#CONFIGS_TO_TEST[@]} -eq 0 ] && [ -n "$SOLVER_CONFIGS" ]; then
    IFS=' ' read -ra CONFIGS_TO_TEST <<< "$SOLVER_CONFIGS"
fi

if [ ${#FILES_TO_TEST[@]} -eq 0 ] && [ -n "$TEST_FILES" ]; then
    IFS=' ' read -ra FILES_TO_TEST <<< "$TEST_FILES"
fi

# Default to all configs if not specified
if [ ${#CONFIGS_TO_TEST[@]} -eq 0 ]; then
    CONFIGS_TO_TEST=("${!SOLVER_ENV_MAP[@]}")
fi

# Get all test files if not specified
if [ ${#FILES_TO_TEST[@]} -eq 0 ]; then
    mapfile -t FILES_TO_TEST < <(find "$SCRIPT_DIR" -name "*.scm" -type f | sort | xargs -n1 basename)
fi

# Colors
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
BLUE='\033[0;34m'
NC='\033[0m'

# Validate configs
for config in "${CONFIGS_TO_TEST[@]}"; do
    if [[ ! -v "SOLVER_ENV_MAP[$config]" ]]; then
        echo -e "${RED}Error: Unknown configuration '$config'${NC}"
        echo "Available: ${!SOLVER_ENV_MAP[*]}"
        exit 1
    fi
done

# Check binary exists
if [ ! -f "$SCRIPT_DIR/$BINARY_NAME" ]; then
    echo "Building binary..."
    make -C "$SCRIPT_DIR" "$BINARY_NAME"
fi

# Show test plan
echo "Test Plan"
echo "========="
echo "Configurations: ${CONFIGS_TO_TEST[*]}"
echo "Files: ${#FILES_TO_TEST[@]}"
echo "Timeout per test: ${TEST_TIMEOUT}s"
echo "Total test combinations: $((${#CONFIGS_TO_TEST[@]} * ${#FILES_TO_TEST[@]}))"
echo ""

if $DRY_RUN; then
    echo "Dry run - not executing tests"
    echo ""
    echo "Would test:"
    for config in "${CONFIGS_TO_TEST[@]}"; do
        echo "  Configuration: $config"
        for file in "${FILES_TO_TEST[@]}"; do
            echo "    - $file"
        done
    done
    exit 0
fi

# Create results directory
mkdir -p "$RESULTS_DIR"
TIMESTAMP=$(date +%Y%m%d_%H%M%S)
SUMMARY_FILE="$RESULTS_DIR/summary_$TIMESTAMP.csv"
DETAILED_FILE="$RESULTS_DIR/detailed_$TIMESTAMP.csv"
REPORT_FILE="$RESULTS_DIR/report_$TIMESTAMP.txt"

# Initialize CSV files
echo "test_file,config,result" > "$SUMMARY_FILE"
echo "test_file,config,result,time,notes" > "$DETAILED_FILE"

# Track results
declare -A CONFIG_PASS_COUNT
declare -A CONFIG_FAIL_COUNT
declare -A CONFIG_TIMEOUT_COUNT
declare -A FILE_RESULTS

# Initialize counters
for config in "${CONFIGS_TO_TEST[@]}"; do
    CONFIG_PASS_COUNT[$config]=0
    CONFIG_FAIL_COUNT[$config]=0
    CONFIG_TIMEOUT_COUNT[$config]=0
done

# Function to run a single test
run_test() {
    local file="$1"
    local env_vars="$2"
    local timeout="$3"
    
    # Build environment variable string
    local env_cmd=""
    if [ -n "$env_vars" ]; then
        IFS=',' read -ra VARS <<< "$env_vars"
        for var in "${VARS[@]}"; do
            env_cmd+=" $var"
        done
    fi
    
    # Run the test with timeout
    local result="PASS"
    local output
    output=$(timeout "$timeout" bash -c "$env_cmd $SCRIPT_DIR/$BINARY_NAME --root-directory $SCRIPT_DIR file $SCRIPT_DIR/$file 2>&1" </dev/null) || {
        if [ $? -eq 124 ]; then
            echo "TIMEOUT"
            return
        fi
    }
    
    if echo "$output" | grep -qi "error\|failed"; then
        echo "FAIL"
    else
        echo "PASS"
    fi
}

# Run tests
total_tests=0
total_pass=0
total_fail=0
total_timeout=0
start_time=$(date +%s)

for config in "${CONFIGS_TO_TEST[@]}"; do
    env_vars="${SOLVER_ENV_MAP[$config]}"
    
    echo -e "${BLUE}========================================${NC}"
    echo -e "${BLUE}Testing configuration: $config${NC}"
    if [ -n "$env_vars" ]; then
        echo -e "${BLUE}Environment: $env_vars${NC}"
    fi
    echo -e "${BLUE}========================================${NC}"
    
    for file in "${FILES_TO_TEST[@]}"; do
        echo -n "  Testing $file... "
        
        test_start=$(date +%s)
        result=$(run_test "$file" "$env_vars" "$TEST_TIMEOUT")
        test_end=$(date +%s)
        duration=$((test_end - test_start))
        
        # Store result
        FILE_RESULTS["$file,$config"]="$result"
        echo "$file,$config,$result,$duration," >> "$DETAILED_FILE"
        echo "$file,$config,$result" >> "$SUMMARY_FILE"
        
        # Update counters
        case $result in
            PASS)
                echo -e "${GREEN}PASS${NC} (${duration}s)"
                CONFIG_PASS_COUNT[$config]=$((${CONFIG_PASS_COUNT[$config]} + 1))
                total_pass=$((total_pass + 1))
                ;;
            TIMEOUT)
                echo -e "${YELLOW}TIMEOUT${NC} (${duration}s)"
                CONFIG_TIMEOUT_COUNT[$config]=$((${CONFIG_TIMEOUT_COUNT[$config]} + 1))
                total_timeout=$((total_timeout + 1))
                ;;
            *)
                echo -e "${RED}FAIL${NC} (${duration}s)"
                CONFIG_FAIL_COUNT[$config]=$((${CONFIG_FAIL_COUNT[$config]} + 1))
                total_fail=$((total_fail + 1))
                ;;
        esac
        
        total_tests=$((total_tests + 1))
        
        # Show progress
        elapsed=$(($(date +%s) - start_time))
        if [ $total_tests -gt 0 ]; then
            avg_time=$((elapsed / total_tests))
            remaining=$((avg_time * (${#CONFIGS_TO_TEST[@]} * ${#FILES_TO_TEST[@]} - total_tests)))
            echo -e "  Progress: $total_tests / $((${#CONFIGS_TO_TEST[@]} * ${#FILES_TO_TEST[@]})) tests"
            echo -e "  Elapsed: $((elapsed / 60))m, ETA: $((remaining / 60))m"
        fi
    done
    echo ""
done

# Generate report
total_elapsed=$(($(date +%s) - start_time))

{
    echo "Solver Configuration Test Report"
    echo "================================"
    echo "Generated: $(date)"
    echo "Total runtime: $((total_elapsed / 60))m $((total_elapsed % 60))s"
    echo ""
    echo "Summary by Configuration:"
    echo "-------------------------"
    printf "%-20s %10s %10s %10s %10s\n" "Configuration" "Passed" "Failed" "Timeout" "Total"
    echo "-------------------------------------------------------"
    
    for config in "${CONFIGS_TO_TEST[@]}"; do
        pass=${CONFIG_PASS_COUNT[$config]}
        fail=${CONFIG_FAIL_COUNT[$config]}
        timeout=${CONFIG_TIMEOUT_COUNT[$config]}
        total=$((pass + fail + timeout))
        printf "%-20s %10d %10d %10d %10d\n" "$config" "$pass" "$fail" "$timeout" "$total"
    done
    
    echo ""
    echo "Overall Statistics:"
    echo "-------------------"
    echo "Total tests: $total_tests"
    echo "Passed: $total_pass"
    echo "Failed: $total_fail"
    echo "Timeout: $total_timeout"
    if [ $total_tests -gt 0 ]; then
        echo "Success rate: $((total_pass * 100 / total_tests))%"
    fi
    echo ""
    echo "File Compatibility Matrix:"
    echo "=========================="
    echo ""
    
    # Show which files pass with which configurations
    for file in "${FILES_TO_TEST[@]}"; do
        echo -n "$file: "
        passing_configs=()
        for config in "${CONFIGS_TO_TEST[@]}"; do
            key="$file,$config"
            if [ "${FILE_RESULTS[$key]}" == "PASS" ]; then
                passing_configs+=("$config")
            fi
        done
        
        if [ ${#passing_configs[@]} -eq ${#CONFIGS_TO_TEST[@]} ]; then
            echo -e "${GREEN}all configs${NC}"
        elif [ ${#passing_configs[@]} -eq 0 ]; then
            echo -e "${RED}none${NC}"
        else
            echo -e "${YELLOW}${passing_configs[*]}${NC}"
        fi
    done
} | tee "$REPORT_FILE"

echo ""
echo "========================================"
echo "Results saved to:"
echo "  Summary:  $SUMMARY_FILE"
echo "  Detailed: $DETAILED_FILE"
echo "  Report:   $REPORT_FILE"
echo "========================================"
