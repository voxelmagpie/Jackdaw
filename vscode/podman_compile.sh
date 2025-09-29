set -e
podman build . -t jackdawvscode
container_id=$(podman create localhost/jackdawvscode)
podman cp "$container_id:/jackdawvscode/jackdaw-highlighting-0.1.0.vsix" .
podman rm "$container_id"
