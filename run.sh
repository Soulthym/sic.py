module=$(echo "${1%.py}" | sed -e 's:/:.:g')
pyright $1
echo "Running $module..."
python -m $module
