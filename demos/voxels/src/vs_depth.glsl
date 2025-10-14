attribute vec4 in_position;

uniform mat4 m;

void main() {
    gl_Position = m * in_position;
}
