// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

attribute vec4 in_position;
attribute vec4 in_normal;
attribute vec4 in_colour;

uniform mat4 model;
uniform mat4 m;
uniform float time;

varying vec4 pass_colour;

void main() {
    vec3 n = (model * in_normal).xyz;
    float light = max(0.0, dot(normalize(vec3(1, 1.3, 0)), n)) * 0.5 + 0.5;
    light *= 1.1;
    pass_colour = vec4(in_colour.rgb * light, in_colour.a);
    vec4 p = in_position;
    if (in_colour.a < 1.0 && p.y == 2.0) {
        p.y = 1.8 + sin(time + p.x*0.5 + p.z*0.5) * 0.1;
    }
    gl_Position = m * p;
}
